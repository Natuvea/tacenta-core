import Translation.TacentaWire
import Translation.WireT1
import Model.CompositeHeader

/-!
# T3 for the ratchet-message decoder: the translated decoder computes what the model says

`Translation/WireT1.lean` proves `decode_composite` cannot fail. This says what
it returns: for every byte string, an `Ok` exactly when `Model.CompositeHeader.decode`
returns `some`, carrying the same header and the same remaining bytes, and an
`Err` exactly when the model returns `none`. The model's decoder is the
specification's, and it applies the same "exactly one spelling" rules as the
code, so refinement here is also canonicality: the code accepts exactly the
byte strings the model accepts.

## The relation

A translated byte is `Std.U8`; the model's is `UInt8`. `byteOf` carries one
across, and a header is carried field by field. The model's numbers are
`UInt32`/`UInt64`/`UInt16` built from shifts and ORs, and the code's are
`from_be_bytes` over a bitvector fold, so the first half of this file is the
arithmetic that says both are the same big-endian sum. It is proved on the
kernel alone; the model's own round-trip lemmas use `bv_decide` for the same
identities, and nothing here depends on them.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.WireT3

open tacenta_wire

/-- One byte across the boundary. -/
def byteOf (b : Std.U8) : UInt8 := UInt8.ofNat b.val

/-- A byte list across the boundary. -/
def bytesOf (l : List Std.U8) : List UInt8 := l.map byteOf

/-- The model's agreement type for a translated one. -/
def agTypeOf : AgreementType → Model.CompositeHeader.AgreementType
  | AgreementType.None => .none
  | AgreementType.Hdr => .hdr
  | AgreementType.Ek => .ek
  | AgreementType.EkCt1Ack => .ekCt1Ack
  | AgreementType.Ct1 => .ct1
  | AgreementType.Ct2 => .ct2

/-- The model's header for a translated one, field by field. -/
def compositeOf (h : Composite) : Model.CompositeHeader.Composite :=
  { dh := bytesOf h.dh.val
    pn := UInt32.ofNat h.pn.val
    n := UInt32.ofNat h.n.val
    pqEpoch := UInt64.ofNat h.pq_epoch.val
    pqN := UInt64.ofNat h.pq_n.val
    agEpoch := UInt64.ofNat h.ag_epoch.val
    agType := agTypeOf h.ag_type
    agChunk := h.ag_chunk.map fun c =>
      { index := UInt16.ofNat c.index.val, data := bytesOf c.data.val } }

/-! ## Big-endian arithmetic on both sides -/

theorem fromLEBytes_nil_toNat : (BitVec.fromLEBytes []).toNat = 0 := by
  simp [BitVec.fromLEBytes]

theorem fromLEBytes_cons_toNat (b : BitVec 8) (l : List (BitVec 8)) :
    (BitVec.fromLEBytes (b :: l)).toNat = b.toNat + 2^8 * (BitVec.fromLEBytes l).toNat := by
  have hb := b.isLt
  have hl := (BitVec.fromLEBytes l).isLt
  have hpow : 2 ^ (8 * (b :: l).length) = 2 ^ (8 * l.length) * 2 ^ 8 := by
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.pow_add]
  have hb' : b.toNat < 2 ^ (8 * (b :: l).length) := by
    rw [hpow]; exact Nat.lt_of_lt_of_le hb (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
  have hl' : (BitVec.fromLEBytes l).toNat % 2 ^ (8 * (b :: l).length) = (BitVec.fromLEBytes l).toNat := by
    apply Nat.mod_eq_of_lt; rw [hpow]
    exact Nat.lt_of_lt_of_le hl (Nat.le_mul_of_pos_right _ (by norm_num))
  have hs : ((BitVec.fromLEBytes l).toNat <<< 8) % 2 ^ (8 * (b :: l).length) = (BitVec.fromLEBytes l).toNat <<< 8 := by
    apply Nat.mod_eq_of_lt; rw [hpow, Nat.shiftLeft_eq]
    exact Nat.mul_lt_mul_of_pos_right hl (by norm_num)
  conv_lhs => unfold BitVec.fromLEBytes
  simp only [BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt hb', hl', hs]
  rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq]
  ring

-- Rust side, through definitional unfolding.
theorem u16_from_be_val (a b : U8) :
    (core.num.U16.from_be_bytes (Array.make 2#usize [a, b])).val = a.val * 2^8 + b.val := by
  show (BitVec.fromLEBytes [b.bv, a.bv]).toNat = _
  simp only [fromLEBytes_cons_toNat, fromLEBytes_nil_toNat, UScalar.val]
  ring

theorem u32_from_be_val (a b c d : U8) :
    (core.num.U32.from_be_bytes (Array.make 4#usize [a, b, c, d])).val =
      a.val * 2^24 + b.val * 2^16 + c.val * 2^8 + d.val := by
  show (BitVec.fromLEBytes [d.bv, c.bv, b.bv, a.bv]).toNat = _
  simp only [fromLEBytes_cons_toNat, fromLEBytes_nil_toNat, UScalar.val]
  ring

-- Model side.
theorem or_shift_step (x y n k : Nat) (hk : n = k + 8) (hy : y < 2 ^ 8) :
    x <<< n ||| y <<< k = (x * 2 ^ 8 + y) <<< k := by
  subst hk
  rw [show x <<< (k + 8) = (x <<< 8) <<< k by rw [Nat.add_comm, Nat.shiftLeft_add],
    ← Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add_eq_or_of_lt hy]
  simp only [Nat.shiftLeft_eq]

theorem or_byte (acc b : Nat) (hb : b < 2 ^ 8) : acc <<< 8 ||| b = acc * 2 ^ 8 + b := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq]

theorem model_be16_toNat (b0 b1 : UInt8) :
    ((b0.toUInt16 <<< 8) ||| b1.toUInt16).toNat = b0.toNat * 2^8 + b1.toNat := by
  have h0 := b0.toNat_lt; have h1 := b1.toNat_lt
  simp only [UInt16.toNat_or, UInt16.toNat_shiftLeft, UInt8.toNat_toUInt16]
  rw [show (8 : UInt16).toNat % 16 = 8 by decide,
    Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega), or_byte _ _ h1]

theorem model_be32_toNat (b0 b1 b2 b3 : UInt8) :
    ((b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) ||| (b2.toUInt32 <<< 8) ||| b3.toUInt32).toNat =
      b0.toNat * 2^24 + b1.toNat * 2^16 + b2.toNat * 2^8 + b3.toNat := by
  have h0 := b0.toNat_lt; have h1 := b1.toNat_lt; have h2 := b2.toNat_lt; have h3 := b3.toNat_lt
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32]
  rw [show (24 : UInt32).toNat % 32 = 24 by decide, show (16 : UInt32).toNat % 32 = 16 by decide,
    show (8 : UInt32).toNat % 32 = 8 by decide]
  rw [Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega),
      Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega),
      Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega)]
  rw [or_shift_step _ _ 24 16 rfl h1, or_shift_step _ _ 16 8 rfl h2, or_byte _ _ h3]
  ring

theorem model_be64_toNat (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    ((b0.toUInt64 <<< 56) ||| (b1.toUInt64 <<< 48) ||| (b2.toUInt64 <<< 40) ||| (b3.toUInt64 <<< 32)
      ||| (b4.toUInt64 <<< 24) ||| (b5.toUInt64 <<< 16) ||| (b6.toUInt64 <<< 8) ||| b7.toUInt64).toNat =
      b0.toNat * 2^56 + b1.toNat * 2^48 + b2.toNat * 2^40 + b3.toNat * 2^32
        + b4.toNat * 2^24 + b5.toNat * 2^16 + b6.toNat * 2^8 + b7.toNat := by
  have h0 := b0.toNat_lt; have h1 := b1.toNat_lt; have h2 := b2.toNat_lt; have h3 := b3.toNat_lt
  have h4 := b4.toNat_lt; have h5 := b5.toNat_lt; have h6 := b6.toNat_lt; have h7 := b7.toNat_lt
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64]
  rw [show (56 : UInt64).toNat % 64 = 56 by decide, show (48 : UInt64).toNat % 64 = 48 by decide,
    show (40 : UInt64).toNat % 64 = 40 by decide, show (32 : UInt64).toNat % 64 = 32 by decide,
    show (24 : UInt64).toNat % 64 = 24 by decide, show (16 : UInt64).toNat % 64 = 16 by decide,
    show (8 : UInt64).toNat % 64 = 8 by decide]
  rw [Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega),
      Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega),
      Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega),
      Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega),
      Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega),
      Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega),
      Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega)]
  rw [or_shift_step _ _ 56 48 rfl h1, or_shift_step _ _ 48 40 rfl h2, or_shift_step _ _ 40 32 rfl h3,
    or_shift_step _ _ 32 24 rfl h4, or_shift_step _ _ 24 16 rfl h5, or_shift_step _ _ 16 8 rfl h6,
    or_byte _ _ h7]
  ring

-- The model's read on any list long enough.
theorem readBe32_of_length (l : List UInt8) (h : 4 ≤ l.length) :
    Model.Messages.readBe32 l =
      some (UInt32.ofNat (l[0]!.toNat * 2^24 + l[1]!.toNat * 2^16 + l[2]!.toNat * 2^8 + l[3]!.toNat), l.drop 4) := by
  match l, h with
  | a :: b :: c :: d :: t, _ =>
    have ha := a.toNat_lt; have hb := b.toNat_lt; have hc := c.toNat_lt; have hd := d.toNat_lt
    simp only [Model.Messages.readBe32]
    congr 2
    apply UInt32.toNat.inj
    rw [model_be32_toNat]
    simp
    omega


/-- An eight-byte big-endian read of any array, as a sum of its bytes. -/
theorem u64_from_be_val (x : Std.Array Std.U8 8#usize) :
    (core.num.U64.from_be_bytes x).val =
      x.val[0]!.val * 2^56 + x.val[1]!.val * 2^48 + x.val[2]!.val * 2^40 + x.val[3]!.val * 2^32
        + x.val[4]!.val * 2^24 + x.val[5]!.val * 2^16 + x.val[6]!.val * 2^8 + x.val[7]!.val := by
  obtain ⟨l, hl⟩ := x
  have hlen : l.length = 8 := by simpa using hl
  match l, hlen with
  | [a, b, c, d, e, f, g, h], _ =>
    show (BitVec.fromLEBytes [h.bv, g.bv, f.bv, e.bv, d.bv, c.bv, b.bv, a.bv]).toNat = _
    simp only [fromLEBytes_cons_toNat, fromLEBytes_nil_toNat, UScalar.val]
    simp
    ring

/-- The model's sixteen-bit read on any list long enough. -/
theorem readBe16_of_length (l : List UInt8) (h : 2 ≤ l.length) :
    Model.CompositeHeader.readBe16 l =
      some (UInt16.ofNat (l[0]!.toNat * 2^8 + l[1]!.toNat), l.drop 2) := by
  match l, h with
  | a :: b :: t, _ =>
    have ha := a.toNat_lt; have hb := b.toNat_lt
    simp only [Model.CompositeHeader.readBe16]
    congr 2
    apply UInt16.toNat.inj
    rw [model_be16_toNat]
    simp
    omega

/-- The model's sixty-four-bit read on any list long enough. -/
theorem readBe64_of_length (l : List UInt8) (h : 8 ≤ l.length) :
    Model.CompositeHeader.readBe64 l =
      some (UInt64.ofNat (l[0]!.toNat * 2^56 + l[1]!.toNat * 2^48 + l[2]!.toNat * 2^40
        + l[3]!.toNat * 2^32 + l[4]!.toNat * 2^24 + l[5]!.toNat * 2^16 + l[6]!.toNat * 2^8
        + l[7]!.toNat), l.drop 8) := by
  match l, h with
  | a :: b :: c :: d :: e :: f :: g :: i :: t, _ =>
    have ha := a.toNat_lt; have hb := b.toNat_lt; have hc := c.toNat_lt; have hd := d.toNat_lt
    have he := e.toNat_lt; have hf := f.toNat_lt; have hg := g.toNat_lt; have hi := i.toNat_lt
    simp only [Model.CompositeHeader.readBe64]
    congr 2
    apply UInt64.toNat.inj
    rw [model_be64_toNat]
    simp
    omega

/-- Splitting a prefix off a list long enough. -/
theorem take?_of_length (n : Nat) (l : List UInt8) (h : n ≤ l.length) :
    Model.Messages.take? n l = some (l.take n, l.drop n) := by
  simp [Model.Messages.take?, Nat.not_lt.mpr h]


/-! ## The agreement type -/

/-- Reading the agreement type returns the model's, or nothing exactly when the
model's does. -/
theorem from_byte_refines (b : Std.U8) :
    ∃ o, AgreementType.from_byte b = ok o ∧
      o.map agTypeOf = Model.CompositeHeader.decodeAgreementType (byteOf b) := by
  unfold AgreementType.from_byte
  split
  all_goals (refine ⟨_, rfl, ?_⟩)
  all_goals (simp only [agTypeOf, byteOf, Option.map, Model.CompositeHeader.decodeAgreementType])
  all_goals (try rfl)
  rename_i h0 h1 h2 h3 h4 h5
  have hb : b.val < 256 := by scalar_tac
  split
  all_goals first
    | rfl
    | (rename_i heq
       have hv := congrArg UInt8.toNat heq
       simp only [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hb] at hv
       simp at hv
       exfalso
       first
         | exact h0 (UScalar.eq_of_val_eq (by rw [hv]; rfl)) | exact h1 (UScalar.eq_of_val_eq (by rw [hv]; rfl))
         | exact h2 (UScalar.eq_of_val_eq (by rw [hv]; rfl)) | exact h3 (UScalar.eq_of_val_eq (by rw [hv]; rfl))
         | exact h4 (UScalar.eq_of_val_eq (by rw [hv]; rfl)) | exact h5 (UScalar.eq_of_val_eq (by rw [hv]; rfl)))

/-- The same, in the form `step*` uses. -/
@[step]
theorem from_byte_spec (b : Std.U8) :
    AgreementType.from_byte b ⦃ o =>
      o.map agTypeOf = Model.CompositeHeader.decodeAgreementType (byteOf b) ⦄ := by
  obtain ⟨o, h, ho⟩ := from_byte_refines b
  rw [h]
  simpa using ho

/-! ## The model's decoder at the header's fixed offsets

`Model.CompositeHeader.decode` is written as a chain of reads, each consuming
the bytes before it. On a list too short for a header every chain ends in
`none`, and on a list long enough every read lands at a fixed offset, so the
decoder is one expression over the list's positions. The code reads the same
positions, which is what the refinement below matches. -/

open Model.CompositeHeader in
section
theorem drop_cons_cons (l : List UInt8) (n : Nat) (h : n + 2 ≤ l.length) :
    l.drop n = l[n]! :: l[n+1]! :: l.drop (n + 2) := by
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : n < l.length),
    List.getElem?_eq_getElem (by omega : n + 1 < l.length)]

theorem take?_none (n : Nat) (l : List UInt8) (h : l.length < n) : Model.Messages.take? n l = none := by
  simp [Model.Messages.take?, h]

theorem readBe32_none (l : List UInt8) (h : l.length < 4) : Model.Messages.readBe32 l = none := by
  match l, h with
  | [], _ | [_], _ | [_, _], _ | [_, _, _], _ => rfl
  | _ :: _ :: _ :: _ :: _, h => simp only [List.length_cons] at h; omega

theorem readBe64_none (l : List UInt8) (h : l.length < 8) : readBe64 l = none := by
  match l, h with
  | [], _ | [_], _ | [_, _], _ | [_, _, _], _ | [_, _, _, _], _ | [_, _, _, _, _], _
  | [_, _, _, _, _, _], _ | [_, _, _, _, _, _, _], _ => rfl
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h => simp only [List.length_cons] at h; omega

theorem readBe16_none (l : List UInt8) (h : l.length < 2) : readBe16 l = none := by
  match l, h with
  | [], _ | [_], _ => rfl
  | _ :: _ :: _, h => simp only [List.length_cons] at h; omega

/-- A check that returns nothing but whether it passed is `none` after it when
what follows it is. -/
theorem bind_unit_none {β : Type} (x : Option Unit) (f : Unit → Option β) (h : f () = none) :
    x.bind f = none := by
  cases x <;> simp [h]

/-- **A list shorter than a header decodes to nothing.** -/
theorem decode_short (l : List UInt8) (h : l.length < 102) : decode l = none := by
  match l, h with
  | [], _ => rfl
  | [_], _ => rfl
  | v :: t :: rest, h =>
    have hr : rest.length < 100 := by simp at h; omega
    simp only [decode]
    split
    · rfl
    split
    · rfl
    simp only [Option.bind_eq_bind]
    by_cases h1 : rest.length < 32
    · simp [take?_none _ _ h1]
    rw [take?_of_length 32 rest (by omega)]; simp only [Option.bind_some]
    -- Whether the ratchet key is canonical does not matter: the header is short.
    apply bind_unit_none
    by_cases h2 : rest.length < 36
    · rw [readBe32_none _ (by simp; omega)]; rfl
    rw [readBe32_of_length _ (by simp; omega)]; simp only [Option.bind_some, List.drop_drop]
    by_cases h3 : rest.length < 40
    · rw [readBe32_none _ (by simp; omega)]; rfl
    rw [readBe32_of_length _ (by simp; omega)]; simp only [Option.bind_some, List.drop_drop]
    by_cases h4 : rest.length < 48
    · rw [readBe64_none _ (by simp; omega)]; rfl
    rw [readBe64_of_length _ (by simp; omega)]; simp only [Option.bind_some, List.drop_drop]
    by_cases h5 : rest.length < 56
    · rw [readBe64_none _ (by simp; omega)]; rfl
    rw [readBe64_of_length _ (by simp; omega)]; simp only [Option.bind_some, List.drop_drop]
    by_cases h6 : rest.length < 64
    · rw [readBe64_none _ (by simp; omega)]; rfl
    rw [readBe64_of_length _ (by simp; omega)]; simp only [Option.bind_some, List.drop_drop]
    by_cases h7 : rest.length < 66
    · split
      · rename_i heq; have := congrArg List.length heq; simp at this; omega
      · rfl
    rw [drop_cons_cons rest (32 + 4 + 4 + 8 + 8 + 8) (by omega)]
    simp only []
    cases decodeAgreementType rest[32 + 4 + 4 + 8 + 8 + 8]! with
    | none => rfl
    | some a =>
      simp only [Option.bind_some]
      by_cases h8 : rest.length < 68
      · rw [readBe16_none _ (by simp; omega)]; rfl
      rw [readBe16_of_length _ (by simp; omega)]; simp only [Option.bind_some]
      rw [take?_none _ _ (by simp [chunkBytes]; omega)]
      rfl

/-- The model's decoder on a list long enough to hold a header, read at the
header's fixed offsets. -/
def decodeLong (l : List UInt8) : Option (Model.CompositeHeader.Composite × List UInt8) :=
  if l[0]! != Model.Messages.version then none
  else if l[1]! != Model.Messages.typeRatchet then none
  else if !Model.Messages.canonicalKey ((l.drop 2).take 32) then none
  else (decodeAgreementType l[66]!).bind fun a =>
    let hdr : Option Model.CompositeHeader.Codeword → Model.CompositeHeader.Composite := fun chunk =>
      { dh := (l.drop 2).take 32
        pn := UInt32.ofNat (l[34]!.toNat * 2^24 + l[35]!.toNat * 2^16 + l[36]!.toNat * 2^8 + l[37]!.toNat)
        n := UInt32.ofNat (l[38]!.toNat * 2^24 + l[39]!.toNat * 2^16 + l[40]!.toNat * 2^8 + l[41]!.toNat)
        pqEpoch := UInt64.ofNat (l[42]!.toNat * 2^56 + l[43]!.toNat * 2^48 + l[44]!.toNat * 2^40
          + l[45]!.toNat * 2^32 + l[46]!.toNat * 2^24 + l[47]!.toNat * 2^16 + l[48]!.toNat * 2^8 + l[49]!.toNat)
        pqN := UInt64.ofNat (l[50]!.toNat * 2^56 + l[51]!.toNat * 2^48 + l[52]!.toNat * 2^40
          + l[53]!.toNat * 2^32 + l[54]!.toNat * 2^24 + l[55]!.toNat * 2^16 + l[56]!.toNat * 2^8 + l[57]!.toNat)
        agEpoch := UInt64.ofNat (l[58]!.toNat * 2^56 + l[59]!.toNat * 2^48 + l[60]!.toNat * 2^40
          + l[61]!.toNat * 2^32 + l[62]!.toNat * 2^24 + l[63]!.toNat * 2^16 + l[64]!.toNat * 2^8 + l[65]!.toNat)
        agType := a
        agChunk := chunk }
    if l[67]! == 1 then
      some (hdr (some { index := UInt16.ofNat (l[68]!.toNat * 2^8 + l[69]!.toNat), data := (l.drop 70).take 32 }),
        l.drop 102)
    else if l[67]! == 0 then
      if (UInt16.ofNat (l[68]!.toNat * 2^8 + l[69]!.toNat) == 0 && ((l.drop 70).take 32).all (· == 0)) then
        some (hdr none, l.drop 102)
      else none
    else none

/-- **A list long enough to hold a header decodes as `decodeLong` says.** -/
theorem decode_long (l : List UInt8) (h : 102 ≤ l.length) : decode l = decodeLong l := by
  match l, h with
  | v :: t :: rest, h =>
    have hr : 100 ≤ rest.length := by simp at h; omega
    conv_lhs => simp only [decode]
    simp only [take?_of_length 32 rest (by omega), Option.bind_eq_bind, Option.bind_some]
    -- The ratchet key: a key that is not canonical is nothing on both sides.
    by_cases hk : Model.Messages.canonicalKey (rest.take 32) = true
    swap
    · have hck : Model.Messages.checkKey (rest.take 32) = none := by
        simp only [Model.Messages.checkKey]
        rw [if_neg hk]
      rw [hck]
      simp [decodeLong, hk]
    have hck : Model.Messages.checkKey (rest.take 32) = some () := by
      simp only [Model.Messages.checkKey]
      rw [if_pos hk]
    rw [hck]
    simp only [Option.bind_some]
    rw [readBe32_of_length _ (by simp; omega)]
    simp only [Option.bind_some]
    rw [readBe32_of_length _ (by simp; omega)]
    simp only [Option.bind_some]
    rw [readBe64_of_length _ (by simp; omega)]
    simp only [Option.bind_some]
    rw [readBe64_of_length _ (by simp; omega)]
    simp only [Option.bind_some]
    rw [readBe64_of_length _ (by simp; omega)]
    simp only [Option.bind_some, List.drop_drop]
    rw [drop_cons_cons rest (32 + 4 + 4 + 8 + 8 + 8) (by omega)]
    simp only []
    rw [readBe16_of_length _ (by simp; omega)]
    simp only [Option.bind_some, List.drop_drop]
    rw [take?_of_length chunkBytes _ (by simp [chunkBytes]; omega)]
    simp only [Option.bind_some, List.drop_drop, decodeLong, chunkBytes]
    simp [hk]

end


/-! ## The code's reads, as values -/

/-- An eight-byte read at `at1` returns the big-endian sum of those eight bytes. -/
@[step]
theorem be64_at_spec (bytes : Slice Std.U8) (at1 : Usize) (h : at1.val + 8 ≤ bytes.length) :
    be64_at bytes at1 ⦃ v => v.val =
      bytes.val[at1.val]!.val * 2^56 + bytes.val[at1.val + 1]!.val * 2^48
        + bytes.val[at1.val + 2]!.val * 2^40 + bytes.val[at1.val + 3]!.val * 2^32
        + bytes.val[at1.val + 4]!.val * 2^24 + bytes.val[at1.val + 5]!.val * 2^16
        + bytes.val[at1.val + 6]!.val * 2^8 + bytes.val[at1.val + 7]!.val ⦄ := by
  unfold be64_at
  step*
  · simp_all [Slice.length, Array.repeat]
  · rw [u64_from_be_val]
    have hlen : s1.val.length = 8 := by simp [s1_post1, List.slice]; scalar_tac
    have hx : (Array.from_slice (Array.repeat 8#usize 0#u8) s1).val = List.slice at1.val (at1.val + 8) bytes.val := by
      rw [Array.from_slice_val _ _ hlen, s1_post1, i_post]
    simp only [s2_post, s_post2, hx, List.slice]
    have hb : at1.val + 8 ≤ bytes.val.length := by simpa [Slice.length] using h
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
    simp (config := { decide := true }) [show ∀ k, k < 8 → at1.val + k < bytes.val.length from fun k hk => by omega]


/-- A byte is zero exactly when its bitvector is. -/
theorem u8_zero_iff (a : U8) : a = 0#u8 ↔ a.bv = 0#8 := by
  rw [UScalar.eq_equiv_bv_eq]; rfl

theorem or_bytes_loop_spec (bytes : Slice U8) (from1 len : Usize) (acc : U8) (i : Usize)
    (hb : from1.val + len.val ≤ bytes.length) (hi : i.val ≤ len.val) :
    or_bytes_loop bytes from1 len acc i ⦃ r =>
      (r = 0#u8 ↔ acc = 0#u8 ∧ ∀ j, i.val ≤ j → j < len.val → bytes.val[from1.val + j]! = 0#u8) ⦄ := by
  unfold or_bytes_loop
  apply loop.spec_decr_nat
    (measure := fun p => len.val - p.2.val)
    (inv := fun p => p.2.val ≤ len.val ∧
      ((p.1 = 0#u8 ∧ ∀ j, p.2.val ≤ j → j < len.val → bytes.val[from1.val + j]! = 0#u8) ↔
       (acc = 0#u8 ∧ ∀ j, i.val ≤ j → j < len.val → bytes.val[from1.val + j]! = 0#u8)))
  · rintro ⟨accA, iA⟩ ⟨hiA, hiff⟩
    unfold or_bytes_loop.body
    simp only [] at hiA hiff ⊢
    split
    · rename_i hlt
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [← hiff]
      have hor : acc1 = 0#u8 ↔ accA = 0#u8 ∧ i2 = 0#u8 := by
        simp only [u8_zero_iff, acc1_post2]
        exact BitVec.or_eq_zero_iff
      have hidx : bytes.val[from1.val + iA.val]! = i2 := by
        rw [i2_post, ← i1_post]
        simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by scalar_tac : i1.val < bytes.val.length)]
      rw [hor]
      constructor
      · rintro ⟨⟨ha, hb2⟩, hall⟩
        refine ⟨ha, fun j hj hjl => ?_⟩
        rcases Nat.eq_or_lt_of_le hj with rfl | hj'
        · rw [hidx]; exact hb2
        · exact hall j (by scalar_tac) hjl
      · rintro ⟨ha, hall⟩
        exact ⟨⟨ha, by rw [← hidx]; exact hall iA.val (le_refl _) (by scalar_tac)⟩,
          fun j hj hjl => hall j (by scalar_tac) hjl⟩
    · rename_i hge
      simp only [WP.spec_ok]
      rw [← hiff]
      have hle : ¬ iA.val < len.val := by scalar_tac
      constructor
      · intro h; exact ⟨h, fun j hj hjl => absurd (Nat.lt_of_le_of_lt hj hjl) hle⟩
      · exact fun h => h.1
  · exact ⟨hi, Iff.rfl⟩


/-- The padding check returns zero exactly when every byte of its range is zero. -/
@[step]
theorem or_bytes_spec (bytes : Slice Std.U8) (from1 len : Usize)
    (h : from1.val + len.val ≤ bytes.length) :
    or_bytes bytes from1 len ⦃ r =>
      (r = 0#u8 ↔ ∀ j, j < len.val → bytes.val[from1.val + j]! = 0#u8) ⦄ := by
  unfold or_bytes
  apply WP.spec_mono (or_bytes_loop_spec bytes from1 len 0#u8 0#usize h (by simp))
  intro r hr
  rw [hr]
  simp

/-- A four-byte big-endian read of four named bytes, as a sum. -/
@[step]
theorem u32_from_be_spec (a b c d : Std.U8) (h : [a, b, c, d].length = (4#usize).val) :
    lift (core.num.U32.from_be_bytes (Array.make 4#usize [a, b, c, d] h)) ⦃ y =>
      y.val = a.val * 2^24 + b.val * 2^16 + c.val * 2^8 + d.val ⦄ := by
  simp only [lift, WP.spec_ok]
  exact u32_from_be_val a b c d

/-- A two-byte big-endian read of two named bytes, as a sum. -/
@[step]
theorem u16_from_be_spec (a b : Std.U8) (h : [a, b].length = (2#usize).val) :
    lift (core.num.U16.from_be_bytes (Array.make 2#usize [a, b] h)) ⦃ y =>
      y.val = a.val * 2^8 + b.val ⦄ := by
  simp only [lift, WP.spec_ok]
  exact u16_from_be_val a b

/-! ## Bytes across the boundary -/

@[simp] theorem bytesOf_length (l : List Std.U8) : (bytesOf l).length = l.length := by
  simp [bytesOf]

@[simp] theorem byteOf_toNat (x : Std.U8) : (byteOf x).toNat = x.val := by
  have := x.hBounds
  simp [byteOf, UInt8.toNat_ofNat']

theorem bytesOf_getElem! (l : List Std.U8) (k : Nat) (hk : k < l.length) :
    (bytesOf l)[k]! = byteOf l[k] := by
  simp [bytesOf, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem byteOf_inj (x y : Std.U8) : byteOf x = byteOf y ↔ x = y := by
  constructor
  · intro h
    have := congrArg UInt8.toNat h
    simp only [byteOf_toNat] at this
    exact UScalar.eq_of_val_eq this
  · rintro rfl; rfl

@[simp] theorem byteOf_version : byteOf VERSION = Model.Messages.version := by
  simp [VERSION, byteOf, Model.Messages.version]

@[simp] theorem byteOf_type_ratchet : byteOf TYPE_RATCHET = Model.Messages.typeRatchet := by
  simp [TYPE_RATCHET, byteOf, Model.Messages.typeRatchet]

theorem bytesOf_drop_take (l : List Std.U8) (a b : Nat) :
    ((bytesOf l).drop a).take b = bytesOf ((l.drop a).take b) := by
  simp [bytesOf, List.map_take, List.map_drop]

theorem bytesOf_drop (l : List Std.U8) (a : Nat) : (bytesOf l).drop a = bytesOf (l.drop a) := by
  simp [bytesOf, List.map_drop]

/-- **The model's canonicity is the code's.** The model says a curve key is
canonical when its bytes, read as a little-endian integer, are below p
(`Model.Messages.canonicalKey`, message-format.md, Curve public keys); the code
checks a byte pattern (`Tacenta.WireT1.canonicalX25519`). On the thirty-two bytes
of an array they agree: `Model.Messages.canonicalKey_bytes` turns the comparison
into the pattern, and what is left is carrying the bytes across the boundary. -/
theorem canonicalKey_bytesOf (k : Std.Array Std.U8 32#usize) :
    Model.Messages.canonicalKey (bytesOf k.val) = Tacenta.WireT1.canonicalX25519 k := by
  have hl : k.val.length = 32 := by simp
  have hb : ∀ j, j < 32 → (bytesOf k.val)[j]!.toNat = (k.val[j]!).val := by
    intro j hj
    rw [bytesOf_getElem! _ _ (by omega), byteOf_toNat]
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : j < k.val.length)]
  have hall : (List.range' 1 30).all (fun j => (bytesOf k.val)[j]!.toNat == 255)
      = Tacenta.WireT1.allFFFrom k 1 := by
    unfold Tacenta.WireT1.allFFFrom
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    constructor
    · intro h j hj
      have hj' := List.mem_range'_1.mp hj
      rw [← hb j (by omega)]
      exact h j (List.mem_range'_1.mpr (by omega))
    · intro h j hj
      have hj' := List.mem_range'_1.mp hj
      rw [hb j (by omega)]
      exact h j (List.mem_range'_1.mpr (by omega))
  have h127 : decide ((k.val[31]!).val = 127) = decide (k.val[31]! = 127#u8) := by
    rw [decide_eq_decide]
    constructor
    · intro h
      exact UScalar.eq_of_val_eq (by simpa using h)
    · intro h
      rw [h]
      rfl
  rw [Model.Messages.canonicalKey_bytes _ (by simp), hb 31 (by omega), hb 0 (by omega), hall, h127]
  rfl

/-- The same, for the thirty-two bytes at `p` that the code copied into `k`. -/
theorem canonicalKey_at (l : List Std.U8) (p : Nat) (k : Std.Array Std.U8 32#usize)
    (hk : k.val = (l.drop p).take 32) :
    Model.Messages.canonicalKey (((bytesOf l).drop p).take 32) = Tacenta.WireT1.canonicalX25519 k := by
  rw [bytesOf_drop_take, ← hk, canonicalKey_bytesOf]

theorem not_eq_true_of_eq_false' {x : Bool} (h : ¬ x = true) : (!x) = true := by
  simpa using h

theorem not_not_eq_true_of_eq_true {x : Bool} (h : x = true) : ¬ (!x) = true := by
  simp [h]

/-- "Every byte of the codeword field is zero", in the model's list form and the
code's indexed form. -/
theorem all_zero_iff (l : List Std.U8) (h : 102 ≤ l.length) :
    (((bytesOf l).drop 70).take 32).all (· == 0) = true ↔ ∀ j, j < 32 → l[70 + j]! = 0#u8 := by
  rw [bytesOf_drop_take, List.all_eq_true]
  constructor
  · intro hall j hj
    have hmem : byteOf l[70 + j]! ∈ bytesOf ((l.drop 70).take 32) := by
      simp only [bytesOf, List.mem_map]
      refine ⟨l[70 + j]!, ?_, rfl⟩
      rw [List.mem_iff_getElem]
      refine ⟨j, by simp; omega, ?_⟩
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : 70 + j < l.length)]
    have := hall _ hmem
    simp only [beq_iff_eq] at this
    have h0 : byteOf l[70 + j]! = byteOf 0#u8 := by rw [this]; rfl
    exact (byteOf_inj _ _).mp h0
  · intro hall x hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have hj' : j < 32 := by simp [bytesOf] at hj; omega
    have hz := hall j hj'
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : 70 + j < l.length)] at hz
    simp only [Option.getD_some] at hz
    simp only [bytesOf, List.getElem_map, List.getElem_take, List.getElem_drop, hz, beq_iff_eq]
    rfl


/-! ## Conditions across the boundary -/

theorem bne_byteOf (x y : Std.U8) : (byteOf x != byteOf y) = (x != y) := by
  rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
  exact not_congr (byteOf_inj x y)

theorem beq_byteOf (x y : Std.U8) : (byteOf x == byteOf y) = (x == y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact byteOf_inj x y

@[simp] theorem byteOf_one : byteOf 1#u8 = 1 := rfl
@[simp] theorem byteOf_zero : byteOf 0#u8 = 0 := rfl

theorem byteOf_beq_one (x : Std.U8) : (byteOf x == 1) = (x == 1#u8) := by
  rw [show (1 : UInt8) = byteOf 1#u8 from rfl, beq_byteOf]

theorem byteOf_beq_zero (x : Std.U8) : (byteOf x == 0) = (x == 0#u8) := by
  rw [show (0 : UInt8) = byteOf 0#u8 from rfl, beq_byteOf]

theorem uint16_ofNat_beq_zero (v : Nat) (h : v < 65536) : (UInt16.ofNat v == 0) = (v == 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · intro e
    have := congrArg UInt16.toNat e
    simpa [UInt16.toNat_ofNat, Nat.mod_eq_of_lt h] using this
  · rintro rfl; rfl

set_option maxHeartbeats 1000000 in
/-- **The translated decoder computes what the model says, on every byte string.**

An `Ok` carries exactly the header `Model.CompositeHeader.decode` returns and
exactly the bytes it leaves unread; an `Err` is exactly the model's `none`.
Since the model accepts one spelling of each header, so does the code: this is
the canonicality the root crate's `tests/canonicality.rs` samples, stated for
every input. No hypothesis, and kernel-only. -/
theorem decode_composite_refines (bytes : Slice Std.U8) :
    decode_composite bytes ⦃ fun r => match r with
      | core.result.Result.Ok p =>
          Model.CompositeHeader.decode (bytesOf bytes.val) = some (compositeOf p.1, bytesOf p.2.val)
      | core.result.Result.Err _ => Model.CompositeHeader.decode (bytesOf bytes.val) = none ⦄ := by
  unfold decode_composite
  simp only [CHUNK_BYTES]
  step*
  all_goals first | (simp_all [Slice.length, Array.repeat]; done) | skip
  all_goals first | (scalar_tac) | skip
  all_goals first
    | (rw [decode_short _ (by simp only [bytesOf_length]; scalar_tac)])
    | skip
  all_goals (
    have hlong : 102 ≤ bytes.val.length := by scalar_tac
    rw [decode_long _ (by simpa using hlong)]
    simp only [decodeLong]
    simp (disch := omega) only [bytesOf_getElem!, ← byteOf_version, ← byteOf_type_ratchet,
      bne_byteOf, byteOf_toNat]
    subst_vars)
  -- refusals on the version and type bytes
  all_goals first
    | (rw [if_pos (by assumption)])
    | (rw [if_neg (by assumption), if_pos (by assumption)])
    | skip
  -- the ratchet key: the code's check is the model's, refused on both sides
  -- or accepted on both
  all_goals (
    have hdhk : (Array.from_slice (Array.repeat 32#usize 0#u8) s2).val = (bytes.val.drop 2).take 32 := by
      rw [Array.from_slice_val _ _ (by simp [s1_post1, List.slice]; omega), s1_post1]; rfl
    rw [canonicalKey_at _ 2 _ hdhk])
  -- A key the code refuses: the check's result is a hypothesis of the branch,
  -- named by its type, since other hypotheses have the same `¬ _ = true` shape.
  all_goals first
    | (rw [if_neg (by assumption), if_neg (by assumption),
        if_pos (not_eq_true_of_eq_false' (by assumption : ¬ Tacenta.WireT1.canonicalX25519
          (Array.from_slice (Array.repeat 32#usize 0#u8) s2) = true))])
    | (have hkt : Tacenta.WireT1.canonicalX25519
          (Array.from_slice (Array.repeat 32#usize 0#u8) s2) = true := by
         rw [← b_post]
       rw [if_neg (by assumption), if_neg (by assumption), hkt, Bool.not_true,
         if_neg Bool.false_ne_true, ← o_post])
  all_goals (simp only [Option.map, Option.bind_some, byteOf_beq_one, byteOf_beq_zero])
  all_goals first | rfl | skip
  all_goals (simp only [bne_iff_ne, ne_eq, not_not, beq_iff_eq] at *)
  -- refusals on the presence byte
  all_goals first
    | (rw [if_neg (by assumption), if_neg (by assumption)])
    | skip
  -- success, codeword present
  on_goal 1 =>
    have hdh : (Array.from_slice (Array.repeat 32#usize 0#u8) s2).val = (bytes.val.drop 2).take 32 := by
      rw [Array.from_slice_val _ _ (by simp [s1_post1, List.slice]; omega), s1_post1]; rfl
    have hdata : (Array.from_slice (Array.repeat 32#usize 0#u8) s5).val = (bytes.val.drop 70).take 32 := by
      rw [Array.from_slice_val _ _ (by simp [s4_post1, List.slice, i15_post]; omega), s4_post1, i15_post]; rfl
    split_ifs <;> try contradiction
    simp only [Option.some.injEq, Prod.mk.injEq, compositeOf, Option.map, hdh, hdata, s6_post1, i1_post,
      pn_post, n_post, index_post, pq_epoch_post, pq_n_post, ag_epoch_post, bytesOf_drop]
    simp (disch := omega) only [getElem!_pos]
    simp only [bytesOf, List.map_take, List.map_drop]
    all_goals trivial
  -- refusal, codeword index not zero
  on_goal 1 =>
    split_ifs <;> first
      | contradiction
      | (rename_i hc
         exfalso
         simp only [Bool.and_eq_true] at hc
         have h16 := hc.1
         rw [uint16_ofNat_beq_zero _ (by scalar_tac), beq_iff_eq] at h16
         have hi0 : index = 0#u16 := UScalar.eq_of_val_eq (by rw [index_post, h16]; rfl)
         contradiction)
      | rfl
  -- refusal, padding not zero
  on_goal 1 =>
    split_ifs <;> first
      | contradiction
      | (rename_i hc
         exfalso
         simp only [Bool.and_eq_true] at hc
         have hz := i15_post.mpr ((all_zero_iff bytes.val hlong).mp hc.2)
         contradiction)
      | rfl
  -- success, codeword absent
  on_goal 1 =>
    have hdh : (Array.from_slice (Array.repeat 32#usize 0#u8) s2).val = (bytes.val.drop 2).take 32 := by
      rw [Array.from_slice_val _ _ (by simp [s1_post1, List.slice]; omega), s1_post1]; rfl
    split_ifs <;> first
      | contradiction
      | (rename_i hnc
         exfalso
         apply hnc
         simp only [Bool.and_eq_true]
         refine ⟨?_, (all_zero_iff bytes.val hlong).mpr (i15_post.mp (by assumption))⟩
         rw [uint16_ofNat_beq_zero _ (by scalar_tac), beq_iff_eq, ← index_post]
         have hi0 : index = 0#u16 := by assumption
         rw [hi0]; rfl)
      | skip
    simp only [Option.some.injEq, Prod.mk.injEq, compositeOf, Option.map, hdh, s3_post1, i1_post,
      pn_post, n_post, pq_epoch_post, pq_n_post, ag_epoch_post, bytesOf_drop]
    simp (disch := omega) only [getElem!_pos]
    simp only [bytesOf, List.map_take, List.map_drop]
    all_goals trivial

/-- **Decoding a ratchet message computes what the model says**: an `Ok` carries
the header the model decodes and, as its ciphertext, exactly the bytes the model
leaves after it; an `Err` is exactly the model's `none`. -/
theorem decode_message_refines (bytes : Slice Std.U8) :
    decode_message bytes ⦃ fun r => match r with
      | core.result.Result.Ok m =>
          Model.CompositeHeader.decode (bytesOf bytes.val) = some (compositeOf m.header, bytesOf m.ciphertext.val)
      | core.result.Result.Err _ => Model.CompositeHeader.decode (bytesOf bytes.val) = none ⦄ := by
  unfold decode_message
  apply WP.spec_bind (decode_composite_refines bytes)
  intro r hr
  cases r with
  | Err e => simpa using hr
  | Ok p =>
    obtain ⟨c, s⟩ := p
    simp only at hr ⊢
    step with alloc.slice.Slice.to_vec_spec
    subst_vars
    exact hr


-- The axiom audit, enforced rather than asserted: both refinements rest on the
-- kernel's three axioms and nothing else. The byte arithmetic above is proved on
-- the kernel, not by `bv_decide`, and the decoder calls no opaque operation. A
-- proof that starts trusting something new fails here.
/-- info: 'Tacenta.WireT3.decode_composite_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.WireT3.decode_composite_refines

/-- info: 'Tacenta.WireT3.decode_message_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.WireT3.decode_message_refines

end Tacenta.WireT3
