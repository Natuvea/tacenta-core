/-
Model.PersistedState: the stored formats of the classical ratchet's state and
of the sparse ratchet's state, byte for byte, the readers that take them back,
and the rules those readers enforce.

Written from tacenta-spec/protocol/session-persistence.md: "Ratchet state",
"Sparse ratchet state", their two entries under "Semantic rules of the leaf
formats", "Stored curve public keys", the Principles section's "Canonical and
length-prefixed", "Versioned" and "Validated, not only parsed", and
"Rejection", which names the two kinds of refusal a leaf reader reports: a
wrong version, and bytes that are short or malformed. A state that breaks a
semantic rule is refused as malformed.

The states are `Model.State.State` and `Model.SparseRatchet.State`, the ones
the operations run on; nothing here adds a field to either. Their counters are
natural numbers and the formats write them in four or eight bytes, so a state
is written faithfully only when every value fits its field and every key is 32
bytes (`RatchetState.Fits`, `SparseState.Fits`).

What is proved, for each format: a state that keeps the rules and fits its
fields is read back from the bytes it is written as (`ofBytes_toBytes`); and a
state the reader returns keeps the rules, fits its fields, and is written as
exactly the bytes it was read from (`ofBytes_ok`), so the reader accepts one
spelling of each state and nothing that breaks a rule.

One thing the page leaves open, and this module therefore decides without a
vector depending on it: which of the two refusals a buffer gets that is too
short for its fixed fields and also carries a version byte other than `0x01`.
The readers here read the version byte first, since the version is what says
how the rest is laid out.
-/
import Model.Erasure
import Model.Messages
import Model.Ratchet
import Model.SparseRatchet

namespace Model.PersistedState

open Model.Erasure (be readBe foldl_be readBe_be)
open Model.Messages (canonicalKey)

abbrev Bytes := List UInt8

-- Both states compared field by field, for the build-time checks below and the
-- vector generator, which writes a state's bytes only when they read back to it.
deriving instance DecidableEq for Model.State.State
deriving instance DecidableEq for Model.SparseRatchet.State

/-! ## Refusals and the reading steps -/

/-- The two refusals a leaf format's reader reports (session-persistence.md,
    Rejection): a version it does not read, and bytes that are short or
    malformed, a state its semantic rules exclude among them. -/
inductive Refusal where
  | wrongVersion
  | shortOrMalformed
  deriving Repr, DecidableEq, Inhabited

/-- The version byte both formats are written with (CONSTANTS.md,
    `STATE_VERSION`). -/
def stateVersion : UInt8 := 0x01

/-- One step of a reader: a value and the bytes after it, or a refusal. -/
abbrev Step (α : Type) := Except Refusal (α × Bytes)

/-- Run the next step on the bytes the previous one left. A function of its
    own rather than `do` notation, so that the proofs below rewrite a step at a
    time. -/
def andThen {α β : Type} (m : Step α) (k : α → Bytes → Except Refusal β) :
    Except Refusal β :=
  match m with
  | .ok (a, rest) => k a rest
  | .error e => .error e

@[simp] theorem andThen_ok {α β : Type} (a : α) (rest : Bytes)
    (k : α → Bytes → Except Refusal β) : andThen (.ok (a, rest)) k = k a rest := rfl

@[simp] theorem andThen_error {α β : Type} (e : Refusal)
    (k : α → Bytes → Except Refusal β) : andThen (.error e) k = .error e := rfl

/-- `n` bytes from the front. -/
def takeN (n : Nat) (bs : Bytes) : Step Bytes :=
  if bs.length < n then .error .shortOrMalformed else .ok (bs.take n, bs.drop n)

/-- A `width`-byte big-endian integer from the front. -/
def readInt (width : Nat) (bs : Bytes) : Step Nat :=
  match readBe width bs with
  | some p => .ok p
  | none => .error .shortOrMalformed

/-- A fixed-width field's bytes read as a big-endian integer. -/
def beValue (bs : Bytes) : Nat := bs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- `count` entries of `width` bytes each, each read by `entry` from exactly its
    own bytes. A count the buffer does not hold is refused. -/
def readEntries {α : Type} (width : Nat) (entry : Bytes → Except Refusal α) :
    Nat → Bytes → Step (List α)
  | 0, bs => .ok ([], bs)
  | n + 1, bs =>
    if bs.length < width then .error .shortOrMalformed
    else
      match entry (bs.take width), readEntries width entry n (bs.drop width) with
      | .ok x, .ok (xs, rest) => .ok (x :: xs, rest)
      | .error e, _ => .error e
      | .ok _, .error e => .error e

/-- A presence byte and a tag's single byte both read `0x00` or `0x01`. -/
def readTag : Bytes → Step Bool
  | [] => .error .shortOrMalformed
  | b :: rest =>
    if b = 0 then .ok (false, rest) else if b = 1 then .ok (true, rest)
    else .error .shortOrMalformed

/-- No two list elements share a key, `key` naming what they must not share. -/
def noShared {α β : Type} [BEq β] (key : α → β) : List α → Bool
  | [] => true
  | x :: xs => !(xs.any fun y => key y == key x) && noShared key xs

/-! ### The steps read back what is written -/

theorem be_length (width n : Nat) : (be width n).length = width := by simp [be]

theorem beValue_be (width n : Nat) (h : n < 256 ^ width) : beValue (be width n) = n := by
  simp only [beValue, foldl_be, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt h]

theorem takeN_append (a rest : Bytes) : takeN a.length (a ++ rest) = .ok (a, rest) := by
  simp [takeN]

theorem takeN_append' (n : Nat) (a rest : Bytes) (h : a.length = n) :
    takeN n (a ++ rest) = .ok (a, rest) := by
  subst h; exact takeN_append a rest

theorem readInt_be (width n : Nat) (rest : Bytes) (h : n < 256 ^ width) :
    readInt width (be width n ++ rest) = .ok (n, rest) := by
  simp [readInt, readBe_be width n rest h]

theorem readEntries_flatten {α : Type} (width : Nat) (enc : α → Bytes)
    (entry : Bytes → Except Refusal α) (xs : List α) (rest : Bytes)
    (hlen : ∀ x ∈ xs, (enc x).length = width) (hdec : ∀ x ∈ xs, entry (enc x) = .ok x) :
    readEntries width entry xs.length ((xs.map enc).flatten ++ rest) = .ok (xs, rest) := by
  induction xs with
  | nil => simp [readEntries]
  | cons x xs ih =>
    have hx := hlen x (by simp)
    have ih' := ih (fun y hy => hlen y (by simp [hy])) (fun y hy => hdec y (by simp [hy]))
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, readEntries]
    rw [if_neg (by simp [hx]), List.take_left' hx, List.drop_left' hx, hdec x (by simp), ih']

/-! ### What a step accepts is what is written -/

theorem andThen_eq_ok {α β : Type} {m : Step α} {k : α → Bytes → Except Refusal β} {b : β}
    (h : andThen m k = .ok b) : ∃ a rest, m = .ok (a, rest) ∧ k a rest = .ok b := by
  rcases m with e | ⟨a, rest⟩
  · simp at h
  · exact ⟨a, rest, rfl, h⟩

theorem takeN_ok {n : Nat} {bs a rest : Bytes} (h : takeN n bs = .ok (a, rest)) :
    a.length = n ∧ bs = a ++ rest := by
  unfold takeN at h
  split at h
  · cases h
  · rename_i hlen
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp only [List.length_take]; omega, (List.take_append_drop n bs).symm⟩

theorem foldl_beValue (l : Bytes) (acc : Nat) :
    l.foldl (fun acc b => acc * 256 + b.toNat) acc = acc * 256 ^ l.length + beValue l := by
  induction l generalizing acc with
  | nil => simp [beValue]
  | cons b t ih =>
    simp only [beValue, List.foldl_cons, List.length_cons]
    rw [ih (acc * 256 + b.toNat), ih (0 * 256 + b.toNat), Nat.pow_succ]
    simp only [beValue]
    generalize 256 ^ t.length = x
    generalize List.foldl (fun acc b => acc * 256 + b.toNat) 0 t = v
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_mul]
    rw [Nat.mul_comm x 256, ← Nat.mul_assoc]
    omega

theorem beValue_cons (b : UInt8) (t : Bytes) :
    beValue (b :: t) = b.toNat * 256 ^ t.length + beValue t := by
  simp only [beValue, List.foldl_cons, Nat.zero_mul, Nat.zero_add]
  rw [foldl_beValue]
  rfl

theorem beValue_lt (l : Bytes) : beValue l < 256 ^ l.length := by
  induction l with
  | nil => simp [beValue]
  | cons b t ih =>
    have hb := b.toNat_lt
    rw [beValue_cons, List.length_cons, Nat.pow_succ]
    have hm : b.toNat * 256 ^ t.length ≤ 255 * 256 ^ t.length :=
      Nat.mul_le_mul_right _ (by omega)
    omega

theorem be_cons (w n : Nat) : be (w + 1) n = UInt8.ofNat (n / 256 ^ w % 256) :: be w n := by
  simp [be, List.range_succ]

theorem be_add_mul (w : Nat) : ∀ c n, be w (c * 256 ^ w + n) = be w n := by
  induction w with
  | zero => intro c n; simp [be]
  | succ w ih =>
    intro c n
    have h1 : c * 256 ^ (w + 1) + n = (c * 256) * 256 ^ w + n := by
      rw [Nat.pow_succ, Nat.mul_comm (256 ^ w) 256, ← Nat.mul_assoc]
    have hpos : 0 < 256 ^ w := Nat.pow_pos (by decide)
    rw [be_cons, be_cons, h1, ih]
    congr 2
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.add_mul_mod_self_right]

theorem be_beValue (l : Bytes) : be l.length (beValue l) = l := by
  induction l with
  | nil => simp [be]
  | cons b t ih =>
    have hpos : 0 < 256 ^ t.length := Nat.pow_pos (by decide)
    have hlt := beValue_lt t
    rw [beValue_cons, List.length_cons, be_cons, be_add_mul, ih,
      Nat.add_comm (b.toNat * 256 ^ t.length), Nat.add_mul_div_right _ _ hpos,
      Nat.div_eq_of_lt hlt, Nat.zero_add, Nat.mod_eq_of_lt b.toNat_lt]
    simp

theorem readInt_ok {w : Nat} {bs : Bytes} {v : Nat} {rest : Bytes}
    (h : readInt w bs = .ok (v, rest)) : v < 256 ^ w ∧ bs = be w v ++ rest := by
  unfold readInt at h
  cases hr : readBe w bs with
  | none => rw [hr] at h; cases h
  | some p =>
    rw [hr] at h
    simp only [Except.ok.injEq] at h
    subst h
    unfold readBe at hr
    split at hr
    · cases hr
    · rename_i hlen
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨hv, hrest⟩ := hr
      have hl : (bs.take w).length = w := by simp only [List.length_take]; omega
      subst hv hrest
      refine ⟨?_, ?_⟩
      · have := beValue_lt (bs.take w); rw [hl] at this; exact this
      · have := be_beValue (bs.take w); rw [hl] at this
        change bs = be w (beValue (bs.take w)) ++ bs.drop w
        rw [this, List.take_append_drop]

theorem readTag_ok {bs : Bytes} {b : Bool} {rest : Bytes} (h : readTag bs = .ok (b, rest)) :
    bs = (if b then 1 else 0) :: rest := by
  match bs, h with
  | [], h => simp [readTag] at h
  | x :: xs, h =>
    simp only [readTag] at h
    split at h
    · rename_i hx
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [hx]
    · split at h
      · rename_i hx
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [hx]
      · cases h

theorem eq_zeros {k : Bytes} {n : Nat} (hl : k.length = n) (h : k.all (· == 0) = true) :
    k = List.replicate n 0 := by
  rw [List.eq_replicate_iff]
  refine ⟨hl, fun b hb => ?_⟩
  have := List.all_eq_true.mp h b hb
  simpa using this

theorem readEntries_ok {α : Type} (width : Nat) (enc : α → Bytes)
    (entry : Bytes → Except Refusal α) (P : α → Prop)
    (hentry : ∀ b x, b.length = width → entry b = .ok x → enc x = b ∧ P x) :
    ∀ (n : Nat) (bs : Bytes) (xs : List α) (rest : Bytes),
      readEntries width entry n bs = .ok (xs, rest) →
        xs.length = n ∧ bs = (xs.map enc).flatten ++ rest ∧ ∀ x ∈ xs, P x := by
  intro n
  induction n with
  | zero =>
    intro bs xs rest h
    simp only [readEntries, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | succ n ih =>
    intro bs xs rest h
    simp only [readEntries] at h
    split at h
    · cases h
    · rename_i hlen
      split at h
      · rename_i x xs' rest' hx hr
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2, h3⟩ := ih _ _ _ hr
        obtain ⟨e1, p1⟩ := hentry _ _ (by simp only [List.length_take]; omega) hx
        refine ⟨by simp [h1], ?_, ?_⟩
        · simp only [List.map_cons, List.flatten_cons, List.append_assoc, e1, ← h2,
            List.take_append_drop]
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact p1
          · exact h3 y hy
      · cases h
      · cases h

theorem take_drop_append (b : Bytes) (m n k : Nat) (h : m + n = k) :
    (b.drop m).take n ++ b.drop k = b.drop m := by
  rw [← h, ← List.drop_drop, List.take_append_drop]

/-! ## Ratchet state

```
ratchet_state = version(1)
             || dhs_pub(32)
             || dhr_pub_present(1) || dhr_pub(32)
             || rk(32)
             || cks_present(1)    || cks(32)
             || ckr_present(1)    || ckr(32)
             || ns(4) || nr(4) || pn(4) || events(4)
             || labels(1)
             || skipped_count(4)
             || skipped[skipped_count]

skipped = dh(32) || n(4) || stored_at(4) || key(32)
```
-/

namespace RatchetState

open Model.State

/-- `u32::MAX`, the value the received-message clock never holds. -/
def u32Max : Nat := 2 ^ 32 - 1

/-- An optional key: a presence byte, `0x00` absent or `0x01` present, and the
    key's full 32 bytes either way, zeroed when absent. -/
def optKeyBytes : Option Key → Bytes
  | none => 0 :: List.replicate 32 0
  | some k => 1 :: k

/-- Refused as malformed: a presence byte other than `0x00` or `0x01`, and an
    absent key whose 32 bytes are not all zero. -/
def readOptKey (bs : Bytes) : Step (Option Key) :=
  andThen (readTag bs) fun present r1 =>
  andThen (takeN 32 r1) fun k r2 =>
    if present then .ok (some k, r2)
    else if k.all (· == 0) then .ok (none, r2)
    else .error .shortOrMalformed

/-- `labels` names the `LabelSet` variant: `0x00`, for the sole `Tacenta` set. -/
def labelsByte : LabelSet → UInt8
  | .tacenta => 0x00

/-- Refused as malformed: a `labels` tag that names no variant, which today is
    any value but `0x00`. -/
def readLabels : Bytes → Step LabelSet
  | [] => .error .shortOrMalformed
  | b :: rest => if b = 0 then .ok (.tacenta, rest) else .error .shortOrMalformed

/-- One stored key: `dh(32) || n(4) || stored_at(4) || key(32)`. -/
def entryBytes (e : Key × Nat × Nat × Key) : Bytes :=
  e.1 ++ be 4 e.2.1 ++ be 4 e.2.2.1 ++ e.2.2.2

/-- One stored key, from exactly its 72 bytes. -/
def readEntry (b : Bytes) : Except Refusal (Key × Nat × Nat × Key) :=
  .ok (b.take 32, beValue ((b.drop 32).take 4), beValue ((b.drop 36).take 4), b.drop 40)

/-- The stored bytes of a state. The stored keys are written in the store's
    order. -/
def toBytes (st : State) : Bytes :=
  [stateVersion] ++ st.dhsPub ++ optKeyBytes st.dhrPub ++ st.rk ++ optKeyBytes st.cks
    ++ optKeyBytes st.ckr ++ be 4 st.ns ++ be 4 st.nr ++ be 4 st.pn ++ be 4 st.events
    ++ [labelsByte st.labels] ++ be 4 st.skipped.length ++ (st.skipped.map entryBytes).flatten

/-! ### Semantic rules (Semantic rules of the leaf formats, Ratchet state) -/

/-- Every curve public key the state holds is its canonical encoding:
    `dhs_pub`, `dhr_pub` when present, and every stored key's `dh`. -/
def keysCanonical (st : State) : Bool :=
  canonicalKey st.dhsPub
    && (match st.dhrPub with | none => true | some k => canonicalKey k)
    && st.skipped.all (fun e => canonicalKey e.1)

/-- The rules, and all of them: the store holds at most `MAX_SKIPPED_STORE`
    keys; `events` is below `u32::MAX`; no stored key's `stored_at` is later
    than `events`; no two stored keys share a ratchet key and message number; a
    receiving chain key is present only if a sending chain key and the peer's
    ratchet public key are; and every curve public key is canonical. Nothing
    constrains `ns`, `nr` or `pn`. -/
def invariant (st : State) : Bool :=
  decide (st.skipped.length ≤ maxSkippedStore)
    && decide (st.events < u32Max)
    && st.skipped.all (fun e => decide (e.2.2.1 ≤ st.events))
    && noShared (fun e => (e.1, e.2.1)) st.skipped
    && (match st.ckr with | none => true | some _ => st.cks.isSome && st.dhrPub.isSome)
    && keysCanonical st

/-! ### The reader -/

/-- Every field after the version byte, in order. -/
def readBody (r0 : Bytes) : Step State :=
  andThen (takeN 32 r0) fun dhsPub r1 =>
  andThen (readOptKey r1) fun dhrPub r2 =>
  andThen (takeN 32 r2) fun rk r3 =>
  andThen (readOptKey r3) fun cks r4 =>
  andThen (readOptKey r4) fun ckr r5 =>
  andThen (readInt 4 r5) fun ns r6 =>
  andThen (readInt 4 r6) fun nr r7 =>
  andThen (readInt 4 r7) fun pn r8 =>
  andThen (readInt 4 r8) fun events r9 =>
  andThen (readLabels r9) fun labels r10 =>
  andThen (readInt 4 r10) fun count r11 =>
  andThen (readEntries 72 readEntry count r11) fun skipped r12 =>
    .ok ({ dhsPub, dhrPub, rk, cks, ckr, ns, nr, pn, skipped, events, labels }, r12)

/-- Read a stored state back. Refused as a wrong version: a first byte other
    than `0x01`. Refused as short or malformed: an empty buffer, a buffer too
    short for a field, a count the buffer does not hold, a bad presence or
    `labels` tag, an absent key not zeroed, bytes after the last stored key,
    and a state that breaks a rule. The stored keys are kept in the order read. -/
def ofBytes : Bytes → Except Refusal State
  | [] => .error .shortOrMalformed
  | v :: body =>
    if v ≠ stateVersion then .error .wrongVersion
    else andThen (readBody body) fun st rest =>
      if rest.isEmpty && invariant st then .ok st else .error .shortOrMalformed

/-- Every value fits its field: each key is 32 bytes, and `ns`, `nr`, `pn` and
    each stored key's `n` are below 2^32. (`events`, each `stored_at` and the
    store's size are below it by the rules.) -/
def Fits (st : State) : Prop :=
  st.dhsPub.length = 32 ∧ (∀ k, st.dhrPub = some k → k.length = 32) ∧ st.rk.length = 32
    ∧ (∀ k, st.cks = some k → k.length = 32) ∧ (∀ k, st.ckr = some k → k.length = 32)
    ∧ st.ns < 2 ^ 32 ∧ st.nr < 2 ^ 32 ∧ st.pn < 2 ^ 32
    ∧ ∀ e ∈ st.skipped, e.1.length = 32 ∧ e.2.1 < 2 ^ 32 ∧ e.2.2.2.length = 32

theorem readTag_cons (b : Bool) (rest : Bytes) :
    readTag ((if b then 1 else 0) :: rest) = .ok (b, rest) := by
  cases b <;> simp [readTag]

theorem readOptKey_bytes (o : Option Key) (rest : Bytes)
    (h : ∀ k, o = some k → k.length = 32) :
    readOptKey (optKeyBytes o ++ rest) = .ok (o, rest) := by
  cases o with
  | none =>
    have := readTag_cons false (List.replicate 32 0 ++ rest)
    simp only [Bool.false_eq_true, if_false] at this
    simp only [optKeyBytes, readOptKey, List.cons_append, this, andThen_ok,
      takeN_append' 32 _ _ (List.length_replicate ..), Bool.false_eq_true, if_false]
    simp
  | some k =>
    have := readTag_cons true (k ++ rest)
    simp only [if_true] at this
    simp only [optKeyBytes, readOptKey, List.cons_append, this, andThen_ok,
      takeN_append' 32 _ _ (h k rfl), if_true]

theorem readEntry_bytes (e : Key × Nat × Nat × Key) (h1 : e.1.length = 32)
    (h2 : e.2.1 < 2 ^ 32) (h3 : e.2.2.1 < 2 ^ 32) :
    readEntry (entryBytes e) = .ok e := by
  obtain ⟨dh, n, at_, k⟩ := e
  simp only at h1 h2 h3
  have hn : n < 256 ^ 4 := by simpa using h2
  have ha : at_ < 256 ^ 4 := by simpa using h3
  simp only [readEntry, entryBytes, List.append_assoc, List.take_left' h1, List.drop_left' h1,
    List.take_left' (be_length 4 n), beValue_be 4 n hn]
  have hd : List.drop 36 (dh ++ (be 4 n ++ (be 4 at_ ++ k))) = be 4 at_ ++ k := by
    rw [show 36 = 32 + 4 from rfl, ← List.drop_drop, List.drop_left' h1, List.drop_left' (be_length 4 n)]
  have hd' : List.drop 40 (dh ++ (be 4 n ++ (be 4 at_ ++ k))) = k := by
    rw [show 40 = 36 + 4 from rfl, ← List.drop_drop, hd, List.drop_left' (be_length 4 at_)]
  rw [hd, hd', List.take_left' (be_length 4 at_), beValue_be 4 at_ ha]

theorem entryBytes_length (e : Key × Nat × Nat × Key) (h1 : e.1.length = 32)
    (h3 : e.2.2.2.length = 32) : (entryBytes e).length = 72 := by
  simp [entryBytes, be_length, h1, h3]

/-- **A state that keeps the rules, and whose values fit their fields, is read
    back from the bytes it is written as.** -/
theorem ofBytes_toBytes (st : State) (hinv : invariant st = true) (hfit : Fits st) :
    ofBytes (toBytes st) = .ok st := by
  obtain ⟨dhsPub, dhrPub, rk, cks, ckr, ns, nr, pn, skipped, events, labels⟩ := st
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hfit
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hinv' := hinv
  simp only [invariant, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hinv'
  obtain ⟨⟨⟨⟨⟨hstore, hev⟩, hat⟩, -⟩, -⟩, -⟩ := hinv'
  have hev4 : events < 256 ^ 4 := by simp only [u32Max] at hev; omega
  have hcount : skipped.length < 256 ^ 4 := by simp only [maxSkippedStore] at hstore; omega
  have hlab : ([labelsByte labels] : Bytes) = [0] := by cases labels; rfl
  have hentries := readEntries_flatten 72 entryBytes readEntry skipped []
    (fun e he => entryBytes_length e (h9 e he).1 (h9 e he).2.2)
    (fun e he => readEntry_bytes e (h9 e he).1 (h9 e he).2.1
      (by have := hat e he; simp only [u32Max] at hev; omega))
  simp only [List.append_nil] at hentries
  simp only [toBytes, ofBytes, stateVersion, List.cons_append, List.nil_append, List.append_assoc, ne_eq, not_true_eq_false, if_false, readBody,
    takeN_append' 32 _ _ h1, andThen_ok, readOptKey_bytes _ _ h2, takeN_append' 32 _ _ h3,
    readOptKey_bytes _ _ h4, readOptKey_bytes _ _ h5,
    readInt_be 4 ns _ (by simpa using h6), readInt_be 4 nr _ (by simpa using h7),
    readInt_be 4 pn _ (by simpa using h8), readInt_be 4 events _ hev4, hlab]
  simp only [readLabels, if_true, andThen_ok]
  rw [readInt_be 4 _ _ hcount]
  simp only [andThen_ok]
  rw [hentries]
  simp only [andThen_ok, List.isEmpty_nil, Bool.true_and]
  rw [if_pos hinv]

theorem readOptKey_ok {bs rest : Bytes} {o : Option Key} (h : readOptKey bs = .ok (o, rest)) :
    (∀ k, o = some k → k.length = 32) ∧ bs = optKeyBytes o ++ rest := by
  unfold readOptKey at h
  obtain ⟨present, r1, h1, hA⟩ := andThen_eq_ok h
  obtain ⟨k, r2, h2, hB⟩ := andThen_eq_ok hA
  obtain ⟨hk, hr1⟩ := takeN_ok h2
  have e1 := readTag_ok h1
  rw [hr1] at e1
  subst e1
  split at hB
  · rename_i hp
    simp only [Except.ok.injEq, Prod.mk.injEq] at hB
    obtain ⟨rfl, rfl⟩ := hB
    refine ⟨fun k' hk' => by (cases hk'; exact hk), ?_⟩
    simp [hp, optKeyBytes]
  · split at hB
    · rename_i hp hz
      simp only [Except.ok.injEq, Prod.mk.injEq] at hB
      obtain ⟨rfl, rfl⟩ := hB
      refine ⟨fun k' hk' => (by cases hk'), ?_⟩
      simp [hp, optKeyBytes, eq_zeros hk hz]
    · cases hB

theorem readLabels_ok {bs rest : Bytes} {l : LabelSet} (h : readLabels bs = .ok (l, rest)) :
    bs = labelsByte l :: rest := by
  match bs, h with
  | [], h => simp [readLabels] at h
  | x :: xs, h =>
    simp only [readLabels] at h
    split at h
    · rename_i hx
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      cases l
      simp [hx, labelsByte]
    · cases h

theorem readEntry_ok {b : Bytes} {e : Key × Nat × Nat × Key} (hl : b.length = 72)
    (h : readEntry b = .ok e) :
    entryBytes e = b ∧ e.1.length = 32 ∧ e.2.1 < 2 ^ 32 ∧ e.2.2.2.length = 32 := by
  simp only [readEntry, Except.ok.injEq] at h
  subst h
  have l4a : ((b.drop 32).take 4).length = 4 := by simp; omega
  have l4b : ((b.drop 36).take 4).length = 4 := by simp; omega
  have ba := be_beValue ((b.drop 32).take 4)
  rw [l4a] at ba
  have bb := be_beValue ((b.drop 36).take 4)
  rw [l4b] at bb
  refine ⟨?_, by simp; omega, ?_, by simp; omega⟩
  · simp only [entryBytes, ba, bb, List.append_assoc]
    rw [take_drop_append b 36 4 40 rfl, take_drop_append b 32 4 36 rfl, List.take_append_drop]
  · have := beValue_lt ((b.drop 32).take 4)
    rw [l4a] at this
    simpa using this

/-- **What the reader accepts is written back as the same bytes**: a state it
    returns keeps the rules and fits its fields, and its stored bytes are the
    bytes it was read from. So the reader accepts one spelling of each state,
    the "Canonical" principle, with no re-encoding check of its own. -/
theorem ofBytes_ok {bs : Bytes} {st : State} (h : ofBytes bs = .ok st) :
    invariant st = true ∧ Fits st ∧ toBytes st = bs := by
  match bs, h with
  | [], h => simp [ofBytes] at h
  | v :: body, h =>
    simp only [ofBytes] at h
    split at h
    · cases h
    · rename_i hv
      have hv' : v = stateVersion := by simpa using hv
      obtain ⟨st', rest, hb, h⟩ := andThen_eq_ok h
      split at h
      · rename_i hc
        simp only [Except.ok.injEq] at h
        subst h
        simp only [Bool.and_eq_true, List.isEmpty_iff] at hc
        obtain ⟨rfl, hinv⟩ := hc
        unfold readBody at hb
        obtain ⟨dhsPub, r1, e1, hb⟩ := andThen_eq_ok hb
        obtain ⟨dhrPub, r2, e2, hb⟩ := andThen_eq_ok hb
        obtain ⟨rk, r3, e3, hb⟩ := andThen_eq_ok hb
        obtain ⟨cks, r4, e4, hb⟩ := andThen_eq_ok hb
        obtain ⟨ckr, r5, e5, hb⟩ := andThen_eq_ok hb
        obtain ⟨ns, r6, e6, hb⟩ := andThen_eq_ok hb
        obtain ⟨nr, r7, e7, hb⟩ := andThen_eq_ok hb
        obtain ⟨pn, r8, e8, hb⟩ := andThen_eq_ok hb
        obtain ⟨events, r9, e9, hb⟩ := andThen_eq_ok hb
        obtain ⟨labels, r10, e10, hb⟩ := andThen_eq_ok hb
        obtain ⟨count, r11, e11, hb⟩ := andThen_eq_ok hb
        obtain ⟨skipped, r12, e12, hb⟩ := andThen_eq_ok hb
        simp only [Except.ok.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        obtain ⟨l1, rfl⟩ := takeN_ok e1
        obtain ⟨k2, rfl⟩ := readOptKey_ok e2
        obtain ⟨l3, rfl⟩ := takeN_ok e3
        obtain ⟨k4, rfl⟩ := readOptKey_ok e4
        obtain ⟨k5, rfl⟩ := readOptKey_ok e5
        obtain ⟨b6, rfl⟩ := readInt_ok e6
        obtain ⟨b7, rfl⟩ := readInt_ok e7
        obtain ⟨b8, rfl⟩ := readInt_ok e8
        obtain ⟨b9, rfl⟩ := readInt_ok e9
        have e10' := readLabels_ok e10
        subst e10'
        obtain ⟨b11, rfl⟩ := readInt_ok e11
        obtain ⟨hlen, rfl, hent⟩ := readEntries_ok 72 entryBytes readEntry
          (fun e => e.1.length = 32 ∧ e.2.1 < 2 ^ 32 ∧ e.2.2.2.length = 32)
          (fun b x hb hx => readEntry_ok hb hx) _ _ _ _ e12
        subst hlen hv'
        refine ⟨hinv, ⟨l1, k2, l3, k4, k5, by simpa using b6, by simpa using b7,
          by simpa using b8, hent⟩, ?_⟩
        simp [toBytes, List.append_assoc]
      · cases h

end RatchetState

/-! ## Sparse ratchet state

```
spqr_state = version(1)
          || rk(32) || epoch(8) || direction(1)
          || chains_count(4) || chains[chains_count]
          || skipped_count(4) || skipped[skipped_count]

chains  = epoch_key(8) || send_chain || receive_chain
chain   = presence(1) || ck(32) || n(8)   -- present, or zeroed if absent
skipped = epoch(8) || n(8) || key(32)
```
-/

namespace SparseState

open Model.SparseRatchet
open Model.State (Key)

/-- `u64::MAX`, where the window's saturating sum stops. -/
def u64Max : Nat := 2 ^ 64 - 1

/-- `a + b`, saturating at `u64::MAX`. -/
def satAdd (a b : Nat) : Nat := min (a + b) u64Max

/-- `direction`: `0x00` `A2b`, `0x01` `B2a`. -/
def directionByte : Direction → UInt8
  | .a2b => 0x00
  | .b2a => 0x01

/-- Refused as malformed: a `direction` tag other than `0x00` or `0x01`. -/
def readDirection (bs : Bytes) : Step Direction :=
  andThen (readTag bs) fun b rest => .ok (if b then .b2a else .a2b, rest)

/-- A chain: a presence byte, then `ck` and `n` at full width, zeroed when
    absent. -/
def chainBytes : Option Chain → Bytes
  | none => 0 :: List.replicate 40 0
  | some c => 1 :: (c.ck ++ be 8 c.n)

/-- A chain, from exactly its 41 bytes. Refused as malformed: a presence byte
    other than `0x00` or `0x01`, and an absent chain whose `ck` and `n` bytes
    are not all zero. An absent chain is accepted. -/
def readChain (b : Bytes) : Except Refusal (Option Chain) :=
  match readTag b with
  | .ok (true, rest) => .ok (some { ck := rest.take 32, n := beValue (rest.drop 32) })
  | .ok (false, rest) => if rest.all (· == 0) then .ok none else .error .shortOrMalformed
  | .error e => .error e

/-- One `chains` entry: `epoch_key(8) || send_chain || receive_chain`. -/
def chainsEntryBytes (p : Nat × Chains) : Bytes :=
  be 8 p.1 ++ chainBytes p.2.send ++ chainBytes p.2.receive

/-- One `chains` entry, from exactly its 90 bytes. -/
def readChainsEntry (b : Bytes) : Except Refusal (Nat × Chains) :=
  match readChain ((b.drop 8).take 41), readChain (b.drop 49) with
  | .ok s, .ok r => .ok (beValue (b.take 8), { send := s, receive := r })
  | .error e, _ => .error e
  | .ok _, .error e => .error e

/-- One stored key: `epoch(8) || n(8) || key(32)`. -/
def skippedBytes (s : Nat × Nat × Key) : Bytes := be 8 s.1 ++ be 8 s.2.1 ++ s.2.2

/-- One stored key, from exactly its 48 bytes. -/
def readSkipped (b : Bytes) : Except Refusal (Nat × Nat × Key) :=
  .ok (beValue (b.take 8), beValue ((b.drop 8).take 8), b.drop 16)

/-- The stored bytes of a state. The `chains` entries and the stored keys are
    written in the state's order. -/
def toBytes (st : State) : Bytes :=
  [stateVersion] ++ st.rk ++ be 8 st.epoch ++ [directionByte st.direction]
    ++ be 4 st.chains.length ++ (st.chains.map chainsEntryBytes).flatten
    ++ be 4 st.skipped.length ++ (st.skipped.map skippedBytes).flatten

/-! ### Semantic rules (Semantic rules of the leaf formats, Sparse ratchet state) -/

/-- The rules, and all of them: the store holds at most `MAX_SKIPPED_STORE`
    keys; every chains entry's epoch `e` satisfies `e <= epoch < e +
    EPOCHS_KEPT`, the sum saturating; no two entries share an epoch; the current
    `epoch` has an entry; every stored key's epoch has an entry; and no two
    stored keys share an epoch and message number. -/
def invariant (st : State) : Bool :=
  decide (st.skipped.length ≤ maxSkippedStore)
    && st.chains.all (fun p => decide (p.1 ≤ st.epoch) && decide (st.epoch < satAdd p.1 epochsKept))
    && noShared Prod.fst st.chains
    && st.chains.any (fun p => p.1 == st.epoch)
    && st.skipped.all (fun s => st.chains.any (fun p => p.1 == s.1))
    && noShared (fun s => (s.1, s.2.1)) st.skipped

/-! ### The reader -/

def readBody (r0 : Bytes) : Step State :=
  andThen (takeN 32 r0) fun rk r1 =>
  andThen (readInt 8 r1) fun epoch r2 =>
  andThen (readDirection r2) fun direction r3 =>
  andThen (readInt 4 r3) fun chainsCount r4 =>
  andThen (readEntries 90 readChainsEntry chainsCount r4) fun chains r5 =>
  andThen (readInt 4 r5) fun skippedCount r6 =>
  andThen (readEntries 48 readSkipped skippedCount r6) fun skipped r7 =>
    .ok ({ rk, epoch, chains, skipped, direction }, r7)

/-- Read a stored state back. Refused as a wrong version: a first byte other
    than `0x01`. Refused as short or malformed: an empty buffer, a buffer too
    short for a field, a count the buffer does not hold, a bad `direction` or
    chain presence tag, an absent chain not zeroed, bytes after the last stored
    key, and a state that breaks a rule. Both lists are kept in the order
    read. -/
def ofBytes : Bytes → Except Refusal State
  | [] => .error .shortOrMalformed
  | v :: body =>
    if v ≠ stateVersion then .error .wrongVersion
    else andThen (readBody body) fun st rest =>
      if rest.isEmpty && invariant st then .ok st else .error .shortOrMalformed

/-- Every value fits its field: each key is 32 bytes, each epoch and chain
    counter is below 2^64, and the chains count below 2^32. (The store's size
    is below it by the rules.) -/
def Fits (st : State) : Prop :=
  st.rk.length = 32 ∧ st.epoch < 2 ^ 64 ∧ st.chains.length < 2 ^ 32
    ∧ (∀ p ∈ st.chains, p.1 < 2 ^ 64
        ∧ (∀ c, p.2.send = some c → c.ck.length = 32 ∧ c.n < 2 ^ 64)
        ∧ (∀ c, p.2.receive = some c → c.ck.length = 32 ∧ c.n < 2 ^ 64))
    ∧ ∀ s ∈ st.skipped, s.1 < 2 ^ 64 ∧ s.2.1 < 2 ^ 64 ∧ s.2.2.length = 32

theorem chainBytes_length (o : Option Chain) (h : ∀ c, o = some c → c.ck.length = 32) :
    (chainBytes o).length = 41 := by
  cases o with
  | none => simp [chainBytes]
  | some c => simp [chainBytes, be_length, h c rfl]

theorem readChain_bytes (o : Option Chain)
    (h : ∀ c, o = some c → c.ck.length = 32 ∧ c.n < 2 ^ 64) :
    readChain (chainBytes o) = .ok o := by
  cases o with
  | none => simp [chainBytes, readChain, readTag]
  | some c =>
    obtain ⟨hck, hn⟩ := h c rfl
    have hn' : c.n < 256 ^ 8 := by simpa using hn
    simp only [chainBytes, readChain, readTag, if_neg (by decide : (1 : UInt8) ≠ 0), if_true,
      List.take_left' hck, List.drop_left' hck, beValue_be 8 c.n hn']

theorem readChainsEntry_bytes (p : Nat × Chains) (h0 : p.1 < 2 ^ 64)
    (hs : ∀ c, p.2.send = some c → c.ck.length = 32 ∧ c.n < 2 ^ 64)
    (hr : ∀ c, p.2.receive = some c → c.ck.length = 32 ∧ c.n < 2 ^ 64) :
    readChainsEntry (chainsEntryBytes p) = .ok p := by
  obtain ⟨e, ⟨s, r⟩⟩ := p
  simp only at h0 hs hr
  have hls := chainBytes_length s (fun c hc => (hs c hc).1)
  have h8 : (be 8 e).length = 8 := be_length 8 e
  have hd8 : List.drop 8 (be 8 e ++ (chainBytes s ++ chainBytes r)) = chainBytes s ++ chainBytes r :=
    List.drop_left' h8
  have hd49 : List.drop 49 (be 8 e ++ (chainBytes s ++ chainBytes r)) = chainBytes r := by
    rw [show 49 = 8 + 41 from rfl, ← List.drop_drop, hd8, List.drop_left' hls]
  simp only [readChainsEntry, chainsEntryBytes, List.append_assoc, hd8, hd49,
    List.take_left' hls, readChain_bytes s hs, readChain_bytes r hr, List.take_left' h8,
    beValue_be 8 e (by simpa using h0)]

theorem chainsEntryBytes_length (p : Nat × Chains)
    (hs : ∀ c, p.2.send = some c → c.ck.length = 32)
    (hr : ∀ c, p.2.receive = some c → c.ck.length = 32) :
    (chainsEntryBytes p).length = 90 := by
  simp [chainsEntryBytes, be_length, chainBytes_length _ hs, chainBytes_length _ hr]

theorem readSkipped_bytes (s : Nat × Nat × Key) (h1 : s.1 < 2 ^ 64) (h2 : s.2.1 < 2 ^ 64) :
    readSkipped (skippedBytes s) = .ok s := by
  obtain ⟨e, n, k⟩ := s
  simp only at h1 h2
  have hd : List.drop 8 (be 8 e ++ (be 8 n ++ k)) = be 8 n ++ k := List.drop_left' (be_length 8 e)
  have hd' : List.drop 16 (be 8 e ++ (be 8 n ++ k)) = k := by
    rw [show 16 = 8 + 8 from rfl, ← List.drop_drop, hd, List.drop_left' (be_length 8 n)]
  simp only [readSkipped, skippedBytes, List.append_assoc, hd, hd',
    List.take_left' (be_length 8 e), List.take_left' (be_length 8 n),
    beValue_be 8 e (by simpa using h1), beValue_be 8 n (by simpa using h2)]

/-- **A state that keeps the rules, and whose values fit their fields, is read
    back from the bytes it is written as.** -/
theorem ofBytes_toBytes (st : State) (hinv : invariant st = true) (hfit : Fits st) :
    ofBytes (toBytes st) = .ok st := by
  obtain ⟨rk, epoch, chains, skipped, direction⟩ := st
  obtain ⟨h1, h2, h3, h4, h5⟩ := hfit
  simp only at h1 h2 h3 h4 h5
  have hstore : skipped.length ≤ maxSkippedStore := by
    simp only [invariant, Bool.and_eq_true, decide_eq_true_eq] at hinv
    exact hinv.1.1.1.1.1
  have hdir : ([directionByte direction] : Bytes) = [if direction = .b2a then 1 else 0] := by
    cases direction <;> rfl
  have hchains := readEntries_flatten 90 chainsEntryBytes readChainsEntry chains
    (be 4 skipped.length ++ (skipped.map skippedBytes).flatten)
    (fun p hp => chainsEntryBytes_length p (fun c hc => ((h4 p hp).2.1 c hc).1)
      (fun c hc => ((h4 p hp).2.2 c hc).1))
    (fun p hp => readChainsEntry_bytes p (h4 p hp).1 (h4 p hp).2.1 (h4 p hp).2.2)
  have hskipped := readEntries_flatten 48 skippedBytes readSkipped skipped []
    (fun s hs => by simp [skippedBytes, be_length, (h5 s hs).2.2])
    (fun s hs => readSkipped_bytes s (h5 s hs).1 (h5 s hs).2.1)
  simp only [List.append_nil] at hskipped
  have hdirRead : readDirection ((if direction = .b2a then (1 : UInt8) else 0) ::
      (be 4 chains.length ++ ((chains.map chainsEntryBytes).flatten ++
        (be 4 skipped.length ++ (skipped.map skippedBytes).flatten)))) =
      .ok (direction, be 4 chains.length ++ ((chains.map chainsEntryBytes).flatten ++
        (be 4 skipped.length ++ (skipped.map skippedBytes).flatten))) := by
    cases direction <;> simp [readDirection, readTag]
  simp only [toBytes, ofBytes, stateVersion, List.cons_append, List.nil_append, List.append_assoc, ne_eq, not_true_eq_false, if_false, readBody, hdir,
    takeN_append' 32 _ _ h1, andThen_ok, readInt_be 8 epoch _ (by simpa using h2)]
  rw [hdirRead]
  simp only [andThen_ok]
  rw [readInt_be 4 _ _ (by simpa using h3)]
  simp only [andThen_ok]
  rw [hchains]
  simp only [andThen_ok]
  rw [readInt_be 4 _ _ (by simp only [maxSkippedStore, Model.State.maxSkippedStore] at hstore; omega)]
  simp only [andThen_ok]
  rw [hskipped]
  simp only [andThen_ok, List.isEmpty_nil, Bool.true_and]
  rw [if_pos hinv]

theorem readDirection_ok {bs rest : Bytes} {d : Direction}
    (h : readDirection bs = .ok (d, rest)) : bs = directionByte d :: rest := by
  unfold readDirection at h
  obtain ⟨b, r, h1, h⟩ := andThen_eq_ok h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rw [readTag_ok h1]
  cases b <;> rfl

theorem readChain_ok {b : Bytes} {o : Option Chain} (hl : b.length = 41)
    (h : readChain b = .ok o) :
    chainBytes o = b ∧ ∀ c, o = some c → c.ck.length = 32 ∧ c.n < 2 ^ 64 := by
  unfold readChain at h
  split at h
  · rename_i rest heq
    have eb := readTag_ok heq
    simp only [Except.ok.injEq] at h
    subst h
    simp only [if_true] at eb
    subst eb
    have hr : rest.length = 40 := by simpa using hl
    have l8 : (rest.drop 32).length = 8 := by simp; omega
    have bb := be_beValue (rest.drop 32)
    rw [l8] at bb
    refine ⟨by simp [chainBytes, bb], fun c hc => ?_⟩
    cases hc
    refine ⟨by simp; omega, ?_⟩
    have := beValue_lt (rest.drop 32)
    rw [l8] at this
    simpa using this
  · rename_i rest heq
    have eb := readTag_ok heq
    split at h
    · rename_i hz
      simp only [Except.ok.injEq] at h
      subst h
      simp only [Bool.false_eq_true, if_false] at eb
      subst eb
      have hr : rest.length = 40 := by simpa using hl
      exact ⟨by simp [chainBytes, eq_zeros hr hz], fun c hc => by cases hc⟩
    · cases h
  · cases h

theorem readChainsEntry_ok {b : Bytes} {p : Nat × Chains} (hl : b.length = 90)
    (h : readChainsEntry b = .ok p) :
    chainsEntryBytes p = b ∧ (p.1 < 2 ^ 64
      ∧ (∀ c, p.2.send = some c → c.ck.length = 32 ∧ c.n < 2 ^ 64)
      ∧ (∀ c, p.2.receive = some c → c.ck.length = 32 ∧ c.n < 2 ^ 64)) := by
  unfold readChainsEntry at h
  split at h
  · rename_i s r hs hr
    simp only [Except.ok.injEq] at h
    subst h
    obtain ⟨es, fs⟩ := readChain_ok (by simp; omega) hs
    obtain ⟨er, fr⟩ := readChain_ok (by simp; omega) hr
    have l8 : (b.take 8).length = 8 := by simp; omega
    have bb := be_beValue (b.take 8)
    rw [l8] at bb
    refine ⟨?_, ?_, fs, fr⟩
    · simp only [chainsEntryBytes, bb, es, er, List.append_assoc]
      rw [take_drop_append b 8 41 49 rfl, List.take_append_drop]
    · have := beValue_lt (b.take 8)
      rw [l8] at this
      simpa using this
  · cases h
  · cases h

theorem readSkipped_ok {b : Bytes} {s : Nat × Nat × Key} (hl : b.length = 48)
    (h : readSkipped b = .ok s) :
    skippedBytes s = b ∧ (s.1 < 2 ^ 64 ∧ s.2.1 < 2 ^ 64 ∧ s.2.2.length = 32) := by
  simp only [readSkipped, Except.ok.injEq] at h
  subst h
  have la : (b.take 8).length = 8 := by simp; omega
  have lb : ((b.drop 8).take 8).length = 8 := by simp; omega
  have ba := be_beValue (b.take 8)
  rw [la] at ba
  have bb := be_beValue ((b.drop 8).take 8)
  rw [lb] at bb
  refine ⟨?_, ?_, ?_, by simp; omega⟩
  · simp only [skippedBytes, ba, bb, List.append_assoc]
    rw [take_drop_append b 8 8 16 rfl, List.take_append_drop]
  · have := beValue_lt (b.take 8)
    rw [la] at this
    simpa using this
  · have := beValue_lt ((b.drop 8).take 8)
    rw [lb] at this
    simpa using this

/-- **What the reader accepts is written back as the same bytes**, as for the
    classical ratchet's state (`RatchetState.ofBytes_ok`). -/
theorem ofBytes_ok {bs : Bytes} {st : State} (h : ofBytes bs = .ok st) :
    invariant st = true ∧ Fits st ∧ toBytes st = bs := by
  match bs, h with
  | [], h => simp [ofBytes] at h
  | v :: body, h =>
    simp only [ofBytes] at h
    split at h
    · cases h
    · rename_i hv
      have hv' : v = stateVersion := by simpa using hv
      obtain ⟨st', rest, hb, h⟩ := andThen_eq_ok h
      split at h
      · rename_i hc
        simp only [Except.ok.injEq] at h
        subst h
        simp only [Bool.and_eq_true, List.isEmpty_iff] at hc
        obtain ⟨rfl, hinv⟩ := hc
        unfold readBody at hb
        obtain ⟨rk, r1, e1, hb⟩ := andThen_eq_ok hb
        obtain ⟨epoch, r2, e2, hb⟩ := andThen_eq_ok hb
        obtain ⟨direction, r3, e3, hb⟩ := andThen_eq_ok hb
        obtain ⟨cc, r4, e4, hb⟩ := andThen_eq_ok hb
        obtain ⟨chains, r5, e5, hb⟩ := andThen_eq_ok hb
        obtain ⟨sc, r6, e6, hb⟩ := andThen_eq_ok hb
        obtain ⟨skipped, r7, e7, hb⟩ := andThen_eq_ok hb
        simp only [Except.ok.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        obtain ⟨l1, rfl⟩ := takeN_ok e1
        obtain ⟨b2, rfl⟩ := readInt_ok e2
        have e3' := readDirection_ok e3
        subst e3'
        obtain ⟨b4, rfl⟩ := readInt_ok e4
        obtain ⟨hl5, rfl, h5⟩ := readEntries_ok 90 chainsEntryBytes readChainsEntry
          (fun p => p.1 < 2 ^ 64
            ∧ (∀ c, p.2.send = some c → c.ck.length = 32 ∧ c.n < 2 ^ 64)
            ∧ (∀ c, p.2.receive = some c → c.ck.length = 32 ∧ c.n < 2 ^ 64))
          (fun b x hb hx => readChainsEntry_ok hb hx) _ _ _ _ e5
        obtain ⟨b6, rfl⟩ := readInt_ok e6
        obtain ⟨hl7, rfl, h7⟩ := readEntries_ok 48 skippedBytes readSkipped
          (fun s => s.1 < 2 ^ 64 ∧ s.2.1 < 2 ^ 64 ∧ s.2.2.length = 32)
          (fun b x hb hx => readSkipped_ok hb hx) _ _ _ _ e7
        subst hl5 hl7 hv'
        refine ⟨hinv, ⟨l1, by simpa using b2, by simpa using b4, h5, h7⟩, ?_⟩
        simp [toBytes, List.append_assoc]
      · cases h

end SparseState

/-! ## Build-time checks

Executable instances of what the text says, as `Model.Erasure`'s are: states the
operations reach read back, and each kind of refusal is the one the page names. -/

/-- Whether a reader returns the state `st`. -/
def readsBackTo {σ : Type} [DecidableEq σ] (r : Except Refusal σ) (st : σ) : Bool :=
  match r with
  | .ok st' => decide (st' = st)
  | .error _ => false

/-- The refusal a reader gives, if it refuses. -/
def refusalOf {σ : Type} (r : Except Refusal σ) : Option Refusal :=
  match r with
  | .ok _ => none
  | .error e => some e

private def sk : Model.State.Key := List.replicate 32 0x01
private def aPub : Model.State.Key := List.replicate 32 0x0a
private def bPub : Model.State.Key := List.replicate 32 0x0b
private def b2Pub : Model.State.Key := List.replicate 32 0x2b
private def dhAB : Model.State.Key := List.replicate 32 0xab
private def dhB2A : Model.State.Key := List.replicate 32 0xba

/-- A responder that received a sender's third message first, so it holds two
    stored keys. -/
private def responderWithStore : Option Model.State.State := do
  let a0 := Model.Ratchet.initSender sk aPub bPub dhAB .tacenta
  let (a1, _, _) ← Model.Ratchet.send a0
  let (a2, _, _) ← Model.Ratchet.send a1
  let (_, h2, _) ← Model.Ratchet.send a2
  let (b1, _) ← Model.Ratchet.receive (Model.Ratchet.initReceiver sk bPub .tacenta) h2 dhAB dhB2A b2Pub
  pure b1

example :
    let a0 := Model.Ratchet.initSender sk aPub bPub dhAB .tacenta
    let b0 := Model.Ratchet.initReceiver sk bPub .tacenta
    readsBackTo (RatchetState.ofBytes (RatchetState.toBytes a0)) a0 &&
      readsBackTo (RatchetState.ofBytes (RatchetState.toBytes b0)) b0 = true := by
  native_decide

example : responderWithStore.map (fun st =>
    (st.skipped.length, readsBackTo (RatchetState.ofBytes (RatchetState.toBytes st)) st))
    = some (2, true) := by
  native_decide

/-- The version byte first; then a bad presence tag, a dirty absent key, a bad
    `labels` tag, a trailing byte and a re-spelled `dhs_pub` are malformed. -/
example :
    let bs := RatchetState.toBytes (Model.Ratchet.initReceiver sk bPub .tacenta)
    refusalOf (RatchetState.ofBytes (bs.set 0 2)) = some .wrongVersion
      ∧ refusalOf (RatchetState.ofBytes (bs.set 33 2)) = some .shortOrMalformed
      ∧ refusalOf (RatchetState.ofBytes (bs.set 34 1)) = some .shortOrMalformed
      ∧ refusalOf (RatchetState.ofBytes (bs.set 180 1)) = some .shortOrMalformed
      ∧ refusalOf (RatchetState.ofBytes (bs ++ [0])) = some .shortOrMalformed
      ∧ refusalOf (RatchetState.ofBytes (bs.set 32 0x8b)) = some .shortOrMalformed
      ∧ refusalOf (RatchetState.ofBytes []) = some .shortOrMalformed := by
  native_decide

example :
    let a0 := Model.SparseRatchet.initAlice sk
    let b0 := Model.SparseRatchet.initBob sk
    readsBackTo (SparseState.ofBytes (SparseState.toBytes a0)) a0 &&
      readsBackTo (SparseState.ofBytes (SparseState.toBytes b0)) b0 = true := by
  native_decide

/-- Bob takes message 3 of epoch 0 first, storing two keys; an epoch later both
    epochs' chains are held, and the bytes read back each time. -/
example :
    (do
      let (b1, _) ← Model.SparseRatchet.receive (Model.SparseRatchet.initBob sk) 0 none 3
      let b2 ← Model.SparseRatchet.advance b1 { keyEpoch := 1, key := List.replicate 32 0xa1 }
      pure (b1.skipped.length, b2.chains.length,
        readsBackTo (SparseState.ofBytes (SparseState.toBytes b1)) b1,
        readsBackTo (SparseState.ofBytes (SparseState.toBytes b2)) b2))
    = some (2, 2, true, true) := by
  native_decide

/-- A `direction` tag of 2, an absent chain that is not zeroed and a state with
    no chains entry for its epoch are malformed; an absent chain that is zeroed
    is accepted. -/
example :
    let a0 := Model.SparseRatchet.initAlice sk
    let bs := SparseState.toBytes a0
    let absent : Model.SparseRatchet.State :=
      { a0 with chains := [(0, { send := none, receive := some { ck := sk, n := 0 } })] }
    refusalOf (SparseState.ofBytes (bs.set 41 2)) = some .shortOrMalformed
      ∧ refusalOf (SparseState.ofBytes ((SparseState.toBytes absent).set 60 1))
          = some .shortOrMalformed
      ∧ readsBackTo (SparseState.ofBytes (SparseState.toBytes absent)) absent = true
      ∧ refusalOf (SparseState.ofBytes (SparseState.toBytes { a0 with epoch := 1 }))
          = some .shortOrMalformed := by
  native_decide

end Model.PersistedState
