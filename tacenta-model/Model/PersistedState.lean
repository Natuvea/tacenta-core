/-
Model.PersistedState: the stored formats of the classical ratchet's state, the
sparse ratchet's state, the Triple Ratchet's state and the ML-KEM Braid's,
byte for byte, the readers that take them back, and the rules those readers
enforce.

Written from tacenta-spec/protocol/session-persistence.md: "Ratchet state",
"Sparse ratchet state", "Triple ratchet state", "Braid", their four entries
under "Semantic rules of the leaf formats", "Stored curve public keys", the
Principles section's "Canonical and length-prefixed", "Versioned" and
"Validated, not only parsed", and "Rejection", which names the two kinds of
refusal a leaf reader reports: a wrong version, and bytes that are short or
malformed. A state that breaks a semantic rule is refused as malformed.

**Where the Braid's model stops, and why it conforms there.** The page
requires of tags 1 to 4 that the `header` and `ek_vector` the stored
`key_pair` holds pass the validation a completed `ek_vector` passes against a
received header, and **scopes that clause to a reader that knows the key
pair's layout** (session-persistence.md, Braid; Semantic rules of the leaf
formats, Braid). Where those two sit inside the 11,872 bytes is
`libcrux-ml-kem`'s layout: the page does not define it and ADR-0006, point 5,
delegates it. So `BraidState` checks `key_pair`'s length and accepts it, which
is what the page asks of a reader outside the scope, as it checks `encaps`'s
length and nothing inside it -- which for `encaps` is the whole of the page's
rule for every implementation, and for `key_pair` is the whole of it only
outside the scope.

The consequence is recorded rather than worked around. For tags 1 to 4 this
reader accepts stored states `tacenta-core`'s refuses, `tacenta-core` having
the layout. Both conform, so a state that fails the clause has no single
conforming verdict and no vector can pin it: no vector generated from this
module offers an accepted state with one of those tags, and the differential
harness offers none either. Tags 0, 5 to 11 carry no `key_pair` and are
modelled in full.

The states are `Model.State.State` and `Model.SparseRatchet.State`, the ones
the operations run on; nothing here adds a field to either. Their counters are
natural numbers and the formats write them in four or eight bytes, so a state
is written faithfully only when every value fits its field and every key is 32
bytes (`RatchetState.Fits`, `SparseState.Fits`).

The operations stop at the ceilings the pages state, so the counters they step
stay inside the fields and the rules: a send leaves `ns` at most `u32::MAX`
(`Model.Ratchet.send_ns_le`), every accepted receive leaves `events` below it
(`Model.Ratchet.receive_events_lt`), an advance leaves the sparse epoch below
`u64::MAX` (`Model.SparseRatchet.advance_epoch_lt`), and a sparse send's new
counter is at most `u64::MAX` (`Model.SparseRatchet.send_number_le`). That the
reader accepts every state the operations produce, in full, is not stated
here: it would also need the key lengths the derivations give, the
canonicality of the curve keys a caller supplies, and the store staying a map.

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
import Model.Braid
import Model.Erasure
import Model.Messages
import Model.Ratchet
import Model.SparseRatchet
import Model.Triple

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

/-- `a + b`, saturating at `u64::MAX` (`Model.SparseRatchet.u64Max`). -/
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

/-! ## Triple ratchet state

```
triple_state = version(1)
            || len(4) || ratchet_state
            || len(4) || spqr_state
```
-/

namespace TripleState

-- Compared field by field, as the two leaf states are, for the build-time
-- checks below and the vector generator.
deriving instance DecidableEq for Model.Triple.State

/-- One length-prefixed field: `len(4) || bytes`. -/
def lenPrefixed (b : Bytes) : Bytes := be 4 b.length ++ b

/-- A length-prefixed field. Refused as malformed: a buffer too short for the
    four-byte length, and a length that overruns what is left. -/
def readLenPrefixed (bs : Bytes) : Step Bytes :=
  andThen (readInt 4 bs) fun n r => takeN n r

/-- The stored bytes: the version byte, then each ratchet's own format,
    length-prefixed and unmodified. -/
def toBytes (st : Model.Triple.State) : Bytes :=
  [stateVersion] ++ lenPrefixed (RatchetState.toBytes st.classical)
    ++ lenPrefixed (SparseState.toBytes st.postQuantum)

/-! ### Semantic rules (Semantic rules of the leaf formats, Triple ratchet
state) -/

/-- The role the classical ratchet still shows: a sending chain and no
    receiving one is the party that sent first, neither is the party that
    received first, and once a Diffie-Hellman step has opened both the state
    shows it no longer (ratchet.md, Initialisation). -/
def startedAsSender (st : Model.State.State) : Option Bool :=
  match st.cks, st.ckr with
  | some _, none => some true
  | none, none => some false
  | _, _ => none

/-- The one rule the composition adds: while the classical ratchet still shows
    the role it started in, the sparse ratchet's `direction` is `A2b` exactly
    when that role is the sender's. Each half's own rules belong to its own
    reader, which is why they are not repeated here. -/
def rolesAgree (st : Model.Triple.State) : Bool :=
  match startedAsSender st.classical with
  | none => true
  | some sender =>
    sender == (st.postQuantum.direction == Model.SparseRatchet.Direction.a2b)

/-- The rules, and all of them: both ratchets satisfy their own, and the two
    halves agree on the role. -/
def invariant (st : Model.Triple.State) : Bool :=
  RatchetState.invariant st.classical && SparseState.invariant st.postQuantum
    && rolesAgree st

/-! ### The reader -/

/-- Read a stored state back. Refused as a wrong version: a first byte other
    than `0x01`. Refused as short or malformed: an empty buffer, a length
    prefix that overruns the input, a half its own reader refuses whatever
    that reader's reason -- an unrecognised inner version included
    (session-persistence.md, Triple ratchet state) -- bytes after the second
    half, and halves that disagree on the role. -/
def ofBytes : Bytes → Except Refusal Model.Triple.State
  | [] => .error .shortOrMalformed
  | v :: body =>
    if v ≠ stateVersion then .error .wrongVersion
    else
      andThen (readLenPrefixed body) fun rs r1 =>
      andThen (readLenPrefixed r1) fun ss r2 =>
        match RatchetState.ofBytes rs with
        | .error _ => .error .shortOrMalformed
        | .ok c =>
          match SparseState.ofBytes ss with
          | .error _ => .error .shortOrMalformed
          | .ok p =>
            let st : Model.Triple.State := { classical := c, postQuantum := p }
            if r2.isEmpty && rolesAgree st then .ok st else .error .shortOrMalformed

/-- Every value fits its field: each half's own do, and each half's stored
    bytes are short enough for the four-byte length written ahead of them. -/
def Fits (st : Model.Triple.State) : Prop :=
  RatchetState.Fits st.classical ∧ SparseState.Fits st.postQuantum
    ∧ (RatchetState.toBytes st.classical).length < 2 ^ 32
    ∧ (SparseState.toBytes st.postQuantum).length < 2 ^ 32

theorem readLenPrefixed_bytes (b rest : Bytes) (h : b.length < 2 ^ 32) :
    readLenPrefixed (lenPrefixed b ++ rest) = .ok (b, rest) := by
  have h' : b.length < 256 ^ 4 := by simpa using h
  simp only [lenPrefixed, readLenPrefixed, List.append_assoc,
    readInt_be 4 b.length (b ++ rest) h', andThen_ok, takeN_append]

theorem readLenPrefixed_ok {bs b rest : Bytes} (h : readLenPrefixed bs = .ok (b, rest)) :
    b.length < 2 ^ 32 ∧ bs = lenPrefixed b ++ rest := by
  unfold readLenPrefixed at h
  obtain ⟨n, r, h1, h2⟩ := andThen_eq_ok h
  obtain ⟨hn, rfl⟩ := readInt_ok h1
  obtain ⟨hl, rfl⟩ := takeN_ok h2
  refine ⟨by rw [hl]; simpa using hn, ?_⟩
  simp [lenPrefixed, hl, List.append_assoc]

/-- **A state that keeps the rules, and whose values fit their fields, is read
    back from the bytes it is written as.** -/
theorem ofBytes_toBytes (st : Model.Triple.State) (hinv : invariant st = true)
    (hfit : Fits st) : ofBytes (toBytes st) = .ok st := by
  obtain ⟨hc, hp, hlc, hlp⟩ := hfit
  have hinv' := hinv
  simp only [invariant, Bool.and_eq_true] at hinv'
  obtain ⟨⟨hic, hip⟩, hroles⟩ := hinv'
  have h1 := readLenPrefixed_bytes (RatchetState.toBytes st.classical)
    (lenPrefixed (SparseState.toBytes st.postQuantum)) hlc
  -- The second half is the last field, so the bytes after it are `[]` rather
  -- than an `++ []` the rewrite would have to see through.
  have h2 := readLenPrefixed_bytes (SparseState.toBytes st.postQuantum) [] hlp
  simp only [List.append_nil] at h2
  simp only [toBytes, ofBytes, stateVersion, List.cons_append, List.nil_append,
    ne_eq, not_true_eq_false, if_false, h1, andThen_ok, h2,
    RatchetState.ofBytes_toBytes _ hic hc, SparseState.ofBytes_toBytes _ hip hp]
  simp [hroles]

/-- **What the reader accepts is written back as the same bytes**, as for the
    two leaf formats (`RatchetState.ofBytes_ok`). -/
theorem ofBytes_ok {bs : Bytes} {st : Model.Triple.State} (h : ofBytes bs = .ok st) :
    invariant st = true ∧ Fits st ∧ toBytes st = bs := by
  match bs, h with
  | [], h => simp [ofBytes] at h
  | v :: body, h =>
    simp only [ofBytes] at h
    split at h
    · cases h
    · rename_i hv
      have hv' : v = stateVersion := by simpa using hv
      obtain ⟨rs, r1, e1, h⟩ := andThen_eq_ok h
      obtain ⟨ss, r2, e2, h⟩ := andThen_eq_ok h
      split at h
      · cases h
      · rename_i c hcok
        split at h
        · cases h
        · rename_i p hpok
          split at h
          · rename_i hok
            simp only [Except.ok.injEq] at h
            subst h
            simp only [Bool.and_eq_true, List.isEmpty_iff] at hok
            obtain ⟨rfl, hroles⟩ := hok
            obtain ⟨hlc, rfl⟩ := readLenPrefixed_ok e1
            obtain ⟨hlp, rfl⟩ := readLenPrefixed_ok e2
            obtain ⟨ic, fc, bc⟩ := RatchetState.ofBytes_ok hcok
            obtain ⟨ip, fp, bp⟩ := SparseState.ofBytes_ok hpok
            subst hv'
            refine ⟨?_, ⟨fc, fp, ?_, ?_⟩, ?_⟩
            · simp only [invariant, Bool.and_eq_true]
              exact ⟨⟨ic, ip⟩, hroles⟩
            · rw [bc]; exact hlc
            · rw [bp]; exact hlp
            · simp [toBytes, bc, bp, stateVersion]
          · cases h

end TripleState

/-! ## Braid

```
braid = version(1) || state_tag(1) || fields

epoch = 8 bytes, big-endian
auth  = root_key(32) || mac_key(32)
```

Every live state carries `epoch` and `auth`, and then the fields its tag
names, each written `len(4) || bytes`. `Failed` (tag 11) carries none of the
three.
-/

namespace BraidState

open Model.Erasure (chunkCount)

/-- The lengths the page gives (session-persistence.md, Braid; CONSTANTS.md,
    Braid KEM field lengths, and KEM key pair and encapsulation state
    lengths). `header`, `ct1` and `ek_vector` are the KEM's values raw;
    `key_pair` and `encaps` are `tacenta-kem`'s own serialisations, whose
    layouts the page delegates and this module therefore only measures. -/
def headerLen : Nat := 64
def ekVectorLen : Nat := 1536
def ct1Len : Nat := 1408
def ct2Len : Nat := 160
def macLen : Nat := 32
def keyPairLen : Nat := 11872
def encapsLen : Nat := 2592

/-- The authenticator's two keys back to back, with no presence tag: every
    live state carries one. -/
def authLen : Nat := 64

/-- `Failed`, the one tag that carries nothing at all, and the largest tag a
    reader accepts. -/
def failedTag : UInt8 := 11

/-- The largest epoch a reader accepts. `u64::MAX` is reserved and refused, so
    a stored live state's epoch runs from 1 to `u64::MAX - 1`
    (session-persistence.md, Braid). -/
def largestEpoch : Nat := Model.Braid.u64Max - 1

/-- What one of a state's length-prefixed fields is. An erasure coder carries
    the length of the value it streams, since the rules size each coder for
    its own value. -/
inductive FieldKind where
  | keyPair
  | encaps
  | header
  | ct1
  | ekVector
  | encoder (valueLen : Nat)
  | decoder (valueLen : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- The fields a tag carries, in the order the page's table writes them. Tag
    11 carries none, and no other tag exists. -/
def kindsOfNat : Nat → List FieldKind
  | 0 => []
  | 1 => [.keyPair, .encoder (headerLen + macLen)]
  | 2 => [.keyPair, .decoder ct1Len, .encoder ekVectorLen]
  | 3 => [.keyPair, .ct1, .encoder ekVectorLen]
  | 4 => [.keyPair, .ct1, .decoder (ct2Len + macLen)]
  | 5 => [.decoder (headerLen + macLen)]
  | 6 => [.header, .decoder ekVectorLen]
  | 7 => [.header, .encaps, .ct1, .encoder ct1Len, .decoder ekVectorLen]
  | 8 => [.encaps, .ct1, .ekVector, .encoder ct1Len]
  | 9 => [.header, .encaps, .ct1, .decoder ekVectorLen]
  | 10 => [.encoder (ct2Len + macLen)]
  | _ => []

def fieldKinds (t : UInt8) : List FieldKind := kindsOfNat t.toNat

/-- What one field must be.

    `header`, `ct1` and `ek_vector` have the lengths the page gives. An
    erasure coder is bytes its own reader accepts, sized for the value it
    streams: an encoder holds `ceil(n / 32)` chunks and a decoder's `size` is
    `n`.

    `key_pair` and `encaps` are length-checked and nothing else. For `encaps`
    that is the whole of the page's rule for every implementation, which says
    the reader "checks nothing in `encaps` beyond its length". For `key_pair`
    it is the whole of the rule only for a reader outside the content clause's
    scope: in tags 1 to 4 the page also requires the `header` and `ek_vector`
    inside it to pass the KEM split's validation, and scopes that clause to a
    reader that knows the layout the page delegates, since finding those two
    needs it. This module has no such layout, so checking the length and
    accepting is what the page asks of it, and stating the clause nowhere is
    conforming rather than short. This reader therefore accepts key pairs
    `tacenta-core` refuses; the module header says what follows. -/
def fieldOk : FieldKind → Bytes → Bool
  | .keyPair, b => decide (b.length = keyPairLen)
  | .encaps, b => decide (b.length = encapsLen)
  | .header, b => decide (b.length = headerLen)
  | .ct1, b => decide (b.length = ct1Len)
  | .ekVector, b => decide (b.length = ekVectorLen)
  | .encoder n, b =>
    match Model.Erasure.Encoder.ofBytes b with
    | some e => decide (e.chunks.length = chunkCount n)
    | none => false
  | .decoder n, b =>
    match Model.Erasure.Decoder.ofBytes b with
    | some d => decide (d.size = n)
    | none => false

/-- A tag's fields, each against its own kind, and as many of them as the tag
    names. -/
def fieldsOk : List FieldKind → List Bytes → Bool
  | [], [] => true
  | k :: ks, f :: fs => fieldOk k f && fieldsOk ks fs
  | _, _ => false

/-- A stored Braid: the tag, the epoch and authenticator every live state
    carries, and the tag's fields in order. `Failed` carries none of the
    three and is written with all three empty. -/
structure State where
  tag : UInt8
  epoch : Nat
  auth : Bytes
  fields : List Bytes
  deriving Repr, DecidableEq, Inhabited

/-- The stored bytes of a state. -/
def toBytes (st : State) : Bytes :=
  if st.tag = failedTag then [stateVersion, st.tag]
  else
    [stateVersion, st.tag] ++ be 8 st.epoch ++ st.auth
      ++ (st.fields.map fun f => be 4 f.length ++ f).flatten

/-! ### Semantic rules (Semantic rules of the leaf formats, Braid) -/

/-- The rules this module states, and all of them: every live state's `epoch`
    is at least 1 and its `auth` is 64 bytes; each tag carries its own fields,
    each of its own kind; and `Failed` is always accepted, carrying nothing.
    The `key_pair` content clause of tags 1 to 4 is not among them: the page
    scopes it to a reader that knows the delegated layout, and this module is
    outside that scope, so omitting it is conforming. `fieldOk` says why. -/
def invariant (st : State) : Bool :=
  if st.tag = failedTag then
    decide (st.epoch = 0) && st.auth.isEmpty && st.fields.isEmpty
  else
    decide (st.tag.toNat < failedTag.toNat)
      && decide (1 ≤ st.epoch)
      && decide (st.auth.length = authLen)
      && fieldsOk (fieldKinds st.tag) st.fields

/-! ### The reader -/

/-- `n` length-prefixed fields, in order. -/
def readFields : Nat → Bytes → Step (List Bytes)
  | 0, bs => .ok ([], bs)
  | n + 1, bs =>
    andThen (readInt 4 bs) fun len r1 =>
    andThen (takeN len r1) fun f r2 =>
    andThen (readFields n r2) fun fs r3 =>
      .ok (f :: fs, r3)

/-- Read a stored state back. Refused as a wrong version: a first byte other
    than `0x01`. Refused as short or malformed: an empty buffer, a buffer with
    no tag, a tag above 11, a stored `epoch` of `u64::MAX` (the reserved
    value), a buffer too short for a field, a length that overruns the input,
    a field its own kind excludes, bytes left after the last field, and a
    state that breaks a rule. Tag 11 is accepted only with nothing after
    it. -/
def ofBytes : Bytes → Except Refusal State
  | [] => .error .shortOrMalformed
  | [v] => if v ≠ stateVersion then .error .wrongVersion else .error .shortOrMalformed
  | v :: t :: body =>
    if v ≠ stateVersion then .error .wrongVersion
    else if t = failedTag then
      if body.isEmpty then .ok { tag := failedTag, epoch := 0, auth := [], fields := [] }
      else .error .shortOrMalformed
    else if failedTag.toNat < t.toNat then .error .shortOrMalformed
    else
      andThen (readInt 8 body) fun epoch r1 =>
      if epoch = Model.Braid.u64Max then .error .shortOrMalformed
      else
        andThen (takeN authLen r1) fun auth r2 =>
        andThen (readFields (fieldKinds t).length r2) fun fields r3 =>
          let st : State := { tag := t, epoch := epoch, auth := auth, fields := fields }
          if r3.isEmpty && invariant st then .ok st else .error .shortOrMalformed

/-- Every value fits its field: the epoch is below the reserved `u64::MAX`,
    which the reader refuses (session-persistence.md, Braid), and every
    field's length fits the four bytes written ahead of it. -/
def Fits (st : State) : Prop :=
  st.epoch < Model.Braid.u64Max ∧ ∀ f ∈ st.fields, f.length < 2 ^ 32

/-! ### The one state machine's transitions a stored state can drive

`Model.Braid` runs on `Model.Braid.BraidState`, whose key pair and
encapsulation state are the KEM's and cannot be built here. Two transitions
are the exception: from `Ct2Sampled`, transition (13) and the refusal at the
reserved epoch read the stored epoch and the message and nothing else, and
`Model.Braid.receive_ct2Sampled_steps` and
`Model.Braid.receive_ct2Sampled_at_ceiling` say so. So a stored `Ct2Sampled`
state can be run through the model's own `receive`, which is what pins the
Braid's epoch ceiling. -/

/-- A stored `Ct2Sampled` state as the state machine's, with an encoder
    neither of those two transitions reads. -/
def toCt2Sampled (st : State) : Option Model.Braid.BraidState :=
  if st.tag.toNat = 10 ∧ st.auth.length = authLen then
    some (.ct2Sampled st.epoch ⟨st.auth.take 32, st.auth.drop 32⟩ (Model.Braid.encode []))
  else none

/-- The stored form of the two states those transitions reach. Every other
    state of the machine carries a KEM value this module does not build, and
    is `none` rather than guessed. -/
def ofBraid : Model.Braid.BraidState → Option State
  | .keysUnsampled e a => some { tag := 0, epoch := e, auth := a.rootKey ++ a.macKey, fields := [] }
  | .failed => some { tag := failedTag, epoch := 0, auth := [], fields := [] }
  | _ => none

theorem readFields_flatten (fs : List Bytes) (rest : Bytes)
    (h : ∀ f ∈ fs, f.length < 2 ^ 32) :
    readFields fs.length ((fs.map fun f => be 4 f.length ++ f).flatten ++ rest)
      = .ok (fs, rest) := by
  induction fs with
  | nil => simp [readFields]
  | cons f fs ih =>
    have hf : f.length < 256 ^ 4 := by simpa using h f (by simp)
    have ih' := ih (fun g hg => h g (by simp [hg]))
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc,
      readFields, readInt_be 4 f.length _ hf, andThen_ok, takeN_append, ih']

theorem readFields_ok : ∀ (n : Nat) (bs : Bytes) (fs : List Bytes) (rest : Bytes),
    readFields n bs = .ok (fs, rest) →
      fs.length = n ∧ bs = (fs.map fun f => be 4 f.length ++ f).flatten ++ rest
        ∧ ∀ f ∈ fs, f.length < 2 ^ 32 := by
  intro n
  induction n with
  | zero =>
    intro bs fs rest h
    simp only [readFields, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | succ n ih =>
    intro bs fs rest h
    simp only [readFields] at h
    obtain ⟨len, r1, e1, h⟩ := andThen_eq_ok h
    obtain ⟨f, r2, e2, h⟩ := andThen_eq_ok h
    obtain ⟨fs', r3, e3, h⟩ := andThen_eq_ok h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hlen, rfl⟩ := readInt_ok e1
    obtain ⟨hf, rfl⟩ := takeN_ok e2
    obtain ⟨h1, rfl, h3⟩ := ih _ _ _ e3
    refine ⟨by simp [h1], ?_, ?_⟩
    · simp only [List.map_cons, List.flatten_cons, List.append_assoc, hf]
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · rw [hf]; simpa using hlen
      · exact h3 g hg

/-- A tag's fields being right of their kinds includes there being as many of
    them as the tag names, which is what lets the reader count fields from the
    tag and the writer count them from the list. -/
theorem fieldsOk_length {ks : List FieldKind} {fs : List Bytes}
    (h : fieldsOk ks fs = true) : ks.length = fs.length := by
  induction ks generalizing fs with
  | nil =>
    cases fs with
    | nil => rfl
    | cons f fs => simp [fieldsOk] at h
  | cons k ks ih =>
    cases fs with
    | nil => simp [fieldsOk] at h
    | cons f fs =>
      simp only [fieldsOk, Bool.and_eq_true] at h
      simp [ih h.2]

/-- **A state that keeps the rules, and whose values fit their fields, is read
    back from the bytes it is written as.** -/
theorem ofBytes_toBytes (st : State) (hinv : invariant st = true) (hfit : Fits st) :
    ofBytes (toBytes st) = .ok st := by
  obtain ⟨hep, hfl⟩ := hfit
  by_cases hfail : st.tag = failedTag
  · have hinv' := hinv
    rw [invariant, if_pos hfail] at hinv'
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hinv'
    obtain ⟨⟨he, ha⟩, hf⟩ := hinv'
    obtain ⟨tag, epoch, auth, fields⟩ := st
    simp only at hfail he ha hf
    subst hfail; subst he; subst ha; subst hf
    simp [toBytes, ofBytes, failedTag, stateVersion]
  · have hinv' := hinv
    rw [invariant, if_neg hfail] at hinv'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hinv'
    obtain ⟨⟨⟨hlt, hge⟩, hauth⟩, hfields⟩ := hinv'
    have hep8 : st.epoch < 256 ^ 8 := by
      simp only [Model.Braid.u64Max] at hep; omega
    have hne : ¬ st.epoch = Model.Braid.u64Max := by omega
    have hflat := readFields_flatten st.fields [] hfl
    simp only [List.append_nil] at hflat
    have hnlt : ¬ failedTag.toNat < st.tag.toNat := by omega
    -- The reader counts the fields from the tag and the writer from the list,
    -- and the rules are what say the two counts agree.
    have hlen : (fieldKinds st.tag).length = st.fields.length := fieldsOk_length hfields
    -- `List.append_assoc` is load-bearing here, whatever the unused-argument
    -- linter says: without it the epoch, the authenticator and the fields stay
    -- bracketed as `toBytes` wrote them and none of the reads below fire.
    set_option linter.unusedSimpArgs false in
    simp only [toBytes, if_neg hfail, ofBytes, stateVersion, List.cons_append,
      List.nil_append, List.append_assoc, ne_eq, not_true_eq_false, if_false,
      if_neg hnlt, readInt_be 8 st.epoch _ hep8, andThen_ok,
      if_neg hne, takeN_append' authLen _ _ hauth, hlen, hflat]
    simp [hinv]

/-- **What the reader accepts is written back as the same bytes**, as for the
    other three formats. -/
theorem ofBytes_ok {bs : Bytes} {st : State} (h : ofBytes bs = .ok st) :
    invariant st = true ∧ Fits st ∧ toBytes st = bs := by
  match bs, h with
  | [], h => simp [ofBytes] at h
  | [v], h =>
    simp only [ofBytes] at h
    split at h <;> cases h
  | v :: t :: body, h =>
    simp only [ofBytes] at h
    split at h
    · cases h
    · rename_i hv
      have hv' : v = stateVersion := by simpa using hv
      split at h
      · rename_i hft
        split at h
        · rename_i hb
          simp only [Except.ok.injEq] at h
          subst h
          simp only [List.isEmpty_iff] at hb
          subst hb; subst hv'; subst hft
          refine ⟨by simp [invariant], ⟨by simp [Model.Braid.u64Max], by simp⟩, ?_⟩
          simp [toBytes, stateVersion]
        · cases h
      · rename_i hft
        split at h
        · cases h
        · rename_i hgt
          obtain ⟨epoch, r1, e1, h⟩ := andThen_eq_ok h
          split at h
          · cases h
          · rename_i hne
            obtain ⟨auth, r2, e2, h⟩ := andThen_eq_ok h
            obtain ⟨fields, r3, e3, h⟩ := andThen_eq_ok h
            split at h
            · rename_i hok
              simp only [Except.ok.injEq] at h
              subst h
              simp only [Bool.and_eq_true, List.isEmpty_iff] at hok
              obtain ⟨rfl, hinv⟩ := hok
              obtain ⟨hb8, rfl⟩ := readInt_ok e1
              obtain ⟨hl2, rfl⟩ := takeN_ok e2
              obtain ⟨hn3, rfl, hf3⟩ := readFields_ok _ _ _ _ e3
              subst hv'
              have hltu : epoch < Model.Braid.u64Max := by
                simp only [Model.Braid.u64Max]
                simp only [Model.Braid.u64Max] at hne
                omega
              refine ⟨hinv, ⟨hltu, hf3⟩, ?_⟩
              simp [toBytes, if_neg hft]
            · cases h

end BraidState

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

/-- A Triple Ratchet state on either side reads back. The version byte first,
    then: a half whose own version byte the inner reader does not recognise is
    short or malformed rather than a wrong version (session-persistence.md,
    Triple ratchet state), and so is a trailing byte. -/
example :
    let a := Model.Triple.initAlice sk aPub bPub dhAB .tacenta
    let b := Model.Triple.initBob sk bPub .tacenta
    let bs := TripleState.toBytes a
    readsBackTo (TripleState.ofBytes bs) a &&
      readsBackTo (TripleState.ofBytes (TripleState.toBytes b)) b &&
      (refusalOf (TripleState.ofBytes (bs.set 0 2)) == some .wrongVersion) &&
      (refusalOf (TripleState.ofBytes (bs.set 5 2)) == some .shortOrMalformed) &&
      (refusalOf (TripleState.ofBytes (bs ++ [0])) == some .shortOrMalformed) = true := by
  native_decide

/-- Halves that disagree on the role are refused, though each half's own reader
    accepts its own bytes: the initiator's classical half beside the
    responder's sparse half. -/
example :
    let a := Model.Triple.initAlice sk aPub bPub dhAB .tacenta
    let b := Model.Triple.initBob sk bPub .tacenta
    let mixed : Model.Triple.State :=
      { classical := a.classical, postQuantum := b.postQuantum }
    refusalOf (TripleState.ofBytes (TripleState.toBytes mixed)) = some .shortOrMalformed := by
  native_decide

/-- A Braid's `Failed` and a live state read back; a tag above 11, the reserved
    epoch `u64::MAX` and an epoch of 0 are malformed. -/
example :
    let auth : Bytes := List.replicate 64 0x07
    let live : BraidState.State := { tag := 0, epoch := 1, auth := auth, fields := [] }
    let failed : BraidState.State := { tag := 11, epoch := 0, auth := [], fields := [] }
    readsBackTo (BraidState.ofBytes (BraidState.toBytes live)) live &&
      readsBackTo (BraidState.ofBytes (BraidState.toBytes failed)) failed &&
      (refusalOf (BraidState.ofBytes (BraidState.toBytes { live with tag := 12 }))
        == some .shortOrMalformed) &&
      (refusalOf (BraidState.ofBytes
          (BraidState.toBytes { live with epoch := Model.Braid.u64Max }))
        == some .shortOrMalformed) &&
      (refusalOf (BraidState.ofBytes (BraidState.toBytes { live with epoch := 0 }))
        == some .shortOrMalformed) = true := by
  native_decide

/-- The Braid's epoch ceiling, driven from stored bytes through the model's own
    `receive`: from `Ct2Sampled` at `u64::MAX - 2` a message at the next epoch
    steps to `KeysUnsampled` there, and the same message at `u64::MAX - 1`
    fails. -/
example :
    let auth : Bytes := List.replicate 64 0x07
    let held (e : Nat) : BraidState.State :=
      { tag := 10, epoch := e, auth := auth,
        fields := [(Model.Erasure.Encoder.new (List.replicate 192 0x11)).toBytes] }
    let step (e msgEpoch : Nat) : Option BraidState.State :=
      (BraidState.toCt2Sampled (held e)).bind fun bst =>
        BraidState.ofBraid (Model.Braid.receive Model.Braid.toyKem bst
          { epoch := msgEpoch, type := Model.Braid.MsgType.none, data := Option.none }).2.2
    (step (Model.Braid.u64Max - 2) (Model.Braid.u64Max - 1)
        == some { tag := 0, epoch := Model.Braid.u64Max - 1, auth := auth, fields := [] }) &&
      (step (Model.Braid.u64Max - 1) Model.Braid.u64Max
        == some { tag := 11, epoch := 0, auth := [], fields := [] }) = true := by
  native_decide

end Model.PersistedState
