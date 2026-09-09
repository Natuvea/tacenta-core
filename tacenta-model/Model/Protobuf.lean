/-
Model.Protobuf: what an accepted byte string means, for one named wire profile.

This is the subject the codec's remaining proof obligations are *about*. Item 1
of the verified-core contract, totality, is a property of the Rust alone and is
proved. Items 3 through 7 are all statements of the form "the Rust agrees with
this", and without this file there is nothing for them to agree with.

Written to mirror the Rust's structure rather than to be elegant. That is
deliberate: the erasure refinement goes through because a partial form is
named on the Lean side that matches the loop's shape on the Rust side, and a
prettier model would need a bridge between the two.

## Not a protobuf specification

It defines the bounded wire profile accepted by this implementation for its two
message types, within the same declared limits the Rust enforces. Anything
outside is not modelled because it is not accepted, and modelling what is
refused would invite implementing it.
-/
import Model.Messages

namespace Model.Protobuf

/-! ## The declared bounds

The same numbers as `tacenta-core/protobuf`, and they are part of the
specification rather than an implementation detail. A decoder that accepted a
longer varint would accept byte strings this model says are not messages, which
is exactly the disagreement item 3 exists to rule out. -/

def maxMessageLen : Nat := 16384
def maxFieldNumber : Nat := 15
def maxFields : Nat := 32
def maxVarintBytes : Nat := 5

/-- The widest value a varint in this profile carries.

Five bytes carry thirty-five bits and the field is thirty-two, so the top three
bits of a maximal varint have nowhere to go. The Rust refuses them, because
every accumulation in it is checked; a model that computed in `Nat` would accept
byte strings the profile does not, and would be wrong in the direction that
matters: claiming a decoder accepts more than it does. -/
def maxU32 : Nat := 4294967295

/-! ## Varints

Base-128, little-endian, minimally encoded. The minimality requirement is the
part with content: without it one value has many spellings, and this profile's
authenticator covers exact bytes, so a second spelling is a second message that
means the same thing. -/

/-- Decode a varint from the front of `bs`, with `factor` the place value of the
    next byte and `acc` the value accumulated so far.

    Three threaded parameters, all three of them the Rust's. `factor` is a
    factor rather than a shift because `checked_shl` reaches the translation as
    an axiom. `fuel` is the Rust's `taken` counting the other way. And `acc` is
    the Rust's `value`. -/
def varintFrom : Nat → Nat → Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, _, _, _ => none
  | fuel + 1, factor, acc, bs =>
    match bs with
    | [] => none
    | b :: rest =>
      let low := (b.toNat) % 128
      let contributed := low * factor
      -- The Rust's `low.checked_mul(factor)`.
      if contributed > maxU32 then none
      else
        let acc' := acc + contributed
        -- The Rust's `value.checked_add(part)`: a running total, not a suffix.
        if acc' > maxU32 then none
        else if b.toNat < 128 then
          -- A final byte. Minimality: a trailing zero byte after the first
          -- contributes nothing and is padding. `factor > 1` is exactly the
          -- Rust's `taken > 1`, since the factor is 128 to the power of the
          -- bytes already taken.
          if factor > 1 && b.toNat == 0 then none else some (acc', rest)
        else
          -- The Rust's `factor.checked_mul(128)`. A place value that has left
          -- the word means no further byte can contribute, and refusing here
          -- rather than carrying `factor = 128 ^ taken` as a side condition is
          -- what keeps the two descriptions comparable without arithmetic that
          -- linear reasoning cannot follow.
          if factor * 128 > maxU32 then none
          else varintFrom fuel (factor * 128) acc' rest

/-- A varint, bounded to the profile's width. -/
def varint (bs : List UInt8) : Option (Nat × List UInt8) :=
  varintFrom maxVarintBytes 1 0 bs

/-! ## Emitting a varint

The inverse direction, and the reason it exists is not symmetry. This profile's
authenticator covers exact bytes, so what matters is that the accepted byte
strings are *exactly* the ones this emits. A round trip -- `decode (encode v) =
v` -- says nothing about that: it constrains what the encoder produces and says
nothing at all about what the decoder accepts. The theorem below goes the other
way. -/

/-- A byte at or above the continuation threshold is its low seven bits plus
    the threshold. Two hundred and fifty-six cases, so the kernel settles it. -/
theorem byte_high (t : UInt8) (h : 128 ≤ t.toNat) :
    t = UInt8.ofNat (t.toNat % 128) + 128 := by
  apply UInt8.toNat_inj.mp
  have hb : t.toNat < 256 := t.toNat_lt
  simp [UInt8.toNat_add, UInt8.toNat_ofNat]
  omega

/-- Emit a varint, minimally, base 128 little-endian. -/
def encodeVarintFrom : Nat → Nat → List UInt8
  | 0, _ => []
  | fuel + 1, v =>
    if v < 128 then [UInt8.ofNat v]
    else UInt8.ofNat (v % 128 + 128) :: encodeVarintFrom fuel (v / 128)

def encodeVarint (v : Nat) : List UInt8 := encodeVarintFrom maxVarintBytes v

/-- **Every accepted byte string is the encoding of what it decodes to.**

    The statement carries three things because the induction needs all three.
    The value is the accumulator plus the part this suffix contributes, scaled
    by the place value. The bytes consumed are exactly that part's encoding. And
    a suffix read at a place value above one contributes *something* -- which is
    the minimality rule doing its work, and is what rules out the trailing zero
    that would give one value a second spelling. -/
theorem varintFrom_canonical (fuel : Nat) :
    ∀ (factor acc : Nat) (bs : List UInt8) (v : Nat) (rest : List UInt8),
    1 ≤ factor →
    varintFrom fuel factor acc bs = some (v, rest) →
    ∃ w, v = acc + w * factor ∧ bs = encodeVarintFrom fuel w ++ rest
         ∧ (1 < factor → 1 ≤ w) := by
  induction fuel with
  | zero => intro factor acc bs v rest _ h; simp [varintFrom] at h
  | succ n ih =>
    intro factor acc bs v rest hf h
    unfold varintFrom at h
    split at h
    · simp at h
    · rename_i b tail _
      repeat' (split at h <;> simp_all)
      -- The final byte: the whole value is this byte's low bits at the current
      -- place value, and minimality is what makes it non-zero.
      · refine ⟨tail.toNat % 128, by omega, ?_, by omega⟩
        have hlt : tail.toNat < 128 := by omega
        simp [encodeVarintFrom, Nat.mod_eq_of_lt hlt, hlt]
      -- A continuation: this byte's low bits, plus everything above it shifted
      -- up one place. The suffix contributes at least one, by induction, which
      -- is what puts this value above 128 and so keeps the encoder in its
      -- continuation branch too.
      · obtain ⟨w, hv, hbs, hpos⟩ := ih (factor * 128) (acc + tail.toNat % 128 * factor)
          _ v rest (by omega) h.2.2.2
        have hw : 1 ≤ w := hpos (by omega)
        refine ⟨tail.toNat % 128 + w * 128, by rw [hv]; simp [Nat.mul_add,
            Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc], ?_, by omega⟩
        have h128 : ¬ (tail.toNat % 128 + w * 128 < 128) := by omega
        simp [encodeVarintFrom, h128, hbs]
        exact ⟨byte_high tail (by omega), by congr 1; omega⟩

theorem varint_canonical (bs : List UInt8) (v : Nat) (rest : List UInt8) :
    varint bs = some (v, rest) → bs = encodeVarint v ++ rest := by
  intro h
  obtain ⟨w, hv, hbs, _⟩ := varintFrom_canonical maxVarintBytes 1 0 bs v rest (by omega) h
  simp at hv
  subst hv
  exact hbs

/-! ## The encoder, against known answers -/

/-- One byte below the threshold is itself. -/
example : encodeVarint 5 = [0x05] := by native_decide

/-- 300 is the canonical two-byte example. -/
example : encodeVarint 300 = [0xAC, 0x02] := by native_decide

/-- Zero is one byte, not none: an empty encoding would be a second spelling of
    a message with the field absent. -/
example : encodeVarint 0 = [0x00] := by native_decide

/-- The widest value the profile carries. -/
example : encodeVarint maxU32 = [0xFF, 0xFF, 0xFF, 0xFF, 0x0F] := by native_decide

/-- And what canonicality means, made concrete: the decoder's own answer, put
    back through the encoder, is the bytes it came from. -/
example : (varint [0xAC, 0x02, 0x77]).map (fun p => encodeVarint p.1 ++ p.2)
    = some [0xAC, 0x02, 0x77] := by native_decide

/-! ## Tags -/

/-- The two wire types this profile carries. -/
inductive WireType where
  | varint
  | lengthDelimited
  deriving Repr, DecidableEq, Inhabited

/-- Interpret a tag value: a field number and a wire type, both in profile.

    Separate from reading one, mirroring the Rust, which split them because a
    totality proof over the fused form carried the varint loop through every
    branch of the interpretation. -/
def decodeTag (raw : Nat) : Option (Nat × WireType) :=
  let field := raw / 8
  let wire := raw % 8
  if field == 0 || field > maxFieldNumber then none
  else if wire == 0 then some (field, WireType.varint)
  else if wire == 2 then some (field, WireType.lengthDelimited)
  else none

/-- Read and interpret a tag. -/
def tag (bs : List UInt8) : Option ((Nat × WireType) × List UInt8) :=
  match varint bs with
  | none => none
  | some (raw, rest) =>
    match decodeTag raw with
    | none => none
    | some t => some (t, rest)

/-! ## Length-delimited fields -/

/-- A length-delimited field's bytes.

    The length is attacker-chosen, so the model checks it against what is
    present exactly as the Rust does. A model that took `bs.take n` without the
    check would accept a truncated message the Rust refuses, and item 3 would
    be false for a reason that is the model's fault rather than the code's. -/
def lengthDelimited (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  match varint bs with
  | none => none
  | some (n, rest) =>
    if rest.length < n then none else some (rest.take n, rest.drop n)

/-! ## Which fields a message has already used

A message-level property, and the first thing in this file that is not about a
single field. Both halves are declared in the Rust; this is what they
enforce. -/

/-- Whether a field number is already recorded.

    `List.contains` would say the same thing and is not what the Rust does: the
    Rust scans by index and stops early, and a model that scanned structurally
    would need that difference bridged before the refinement could start. This
    is the same foresight `varintFrom` needed and for the same reason. -/
def seenFrom : Nat → List Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, seen, field =>
    match seen with
    | [] => false
    | s :: rest => if s == field then true else seenFrom fuel rest field

/-- Whether a field number is already recorded, scanning all of it. -/
def seen (xs : List Nat) (field : Nat) : Bool := seenFrom xs.length xs field

/-- Record a field number, or refuse.

    Two refusals with different reasons and the same consequence: the message
    is not one this profile accepts. A duplicate is refused rather than
    resolved, because "take the last" would make a message's meaning depend on
    the order a decoder happens to read it in. -/
def admit (xs : List Nat) (field : Nat) : Option (List Nat) :=
  if seen xs field then none
  else if xs.length ≥ maxFields then none
  else some (xs ++ [field])

/-! ## Known answers for the field set -/

/-- A fresh set has nothing in it. -/
example : seen [] 3 = false := by native_decide

/-- What was admitted is then present. -/
example : (admit [] 3).map (fun xs => seen xs 3) = some true := by native_decide

/-- And cannot be admitted twice. -/
example : (admit [3] 3) = none := by native_decide

/-- A different field still can be. -/
example : admit [3] 4 = some [3, 4] := by native_decide

/-- The profile's field limit is enforced, not merely declared. -/
example : admit (List.replicate maxFields 0 |>.zipIdx.map (fun p => p.2 + 1)) 99 = none := by
  native_decide

/-! ## The ratchet message profile

The field numbers and wire types are those of the external interoperability
profile (`tacenta-spec/CONSTANTS.md`).

This is the first thing here that describes a *message* rather than a piece of
one, and it is where three policies stop being code and become specification:
field order is free, a repeated field is refused, and an absent field is refused
rather than defaulted. -/

def fieldRatchetKey : Nat := 1
def fieldCounter : Nat := 2
def fieldPreviousCounter : Nat := 3
def fieldCiphertext : Nat := 4
def fieldPq : Nat := 5

/-- A parsed ratchet message. -/
structure RatchetBody where
  ratchetKey : List UInt8
  counter : Nat
  previousCounter : Nat
  ciphertext : List UInt8
  pq : List UInt8
  deriving Repr, DecidableEq, Inhabited

/-- The parse in progress.

    `refused` is a flag rather than an error kind, matching the rest of this
    file: what an accepted byte string means is the subject, and *which* refusal
    a rejected one earns is the code's business. -/
structure ParseState where
  rest : List UInt8
  seen : List Nat
  ratchetKey : List UInt8
  counter : Nat
  previousCounter : Nat
  ciphertext : List UInt8
  pq : List UInt8
  refused : Bool
  deriving Repr, Inhabited

/-- Read one field into the state.

    Mirrors `one_field`, including that a refusal leaves the rest of the state
    alone. A wire type that does not match the field's is refused rather than
    skipped: a byte string whose meaning nobody has defined is not a message. -/
def oneField (st : ParseState) : ParseState :=
  match tag st.rest with
  | none => { st with refused := true }
  | some ((field, wire), rest1) =>
    match admit st.seen field with
    | none => { st with rest := rest1, refused := true }
    | some seen1 =>
      let st1 := { st with rest := rest1, seen := seen1 }
      if field == fieldRatchetKey then
        match wire with
        | WireType.lengthDelimited =>
          match lengthDelimited rest1 with
          | none => { st1 with refused := true }
          | some (v, rest2) => { st1 with rest := rest2, ratchetKey := v }
        | _ => { st1 with refused := true }
      else if field == fieldCounter then
        match wire with
        | WireType.varint =>
          match varint rest1 with
          | none => { st1 with refused := true }
          | some (v, rest2) => { st1 with rest := rest2, counter := v }
        | _ => { st1 with refused := true }
      else if field == fieldPreviousCounter then
        match wire with
        | WireType.varint =>
          match varint rest1 with
          | none => { st1 with refused := true }
          | some (v, rest2) => { st1 with rest := rest2, previousCounter := v }
        | _ => { st1 with refused := true }
      else if field == fieldCiphertext then
        match wire with
        | WireType.lengthDelimited =>
          match lengthDelimited rest1 with
          | none => { st1 with refused := true }
          | some (v, rest2) => { st1 with rest := rest2, ciphertext := v }
        | _ => { st1 with refused := true }
      else if field == fieldPq then
        match wire with
        | WireType.lengthDelimited =>
          match lengthDelimited rest1 with
          | none => { st1 with refused := true }
          | some (v, rest2) => { st1 with rest := rest2, pq := v }
        | _ => { st1 with refused := true }
      else { st1 with refused := true }

/-- Read fields until refusal, exhaustion, or the field bound. -/
def parseFrom : Nat → ParseState → ParseState
  | 0, st => st
  | fuel + 1, st =>
    if st.refused || st.rest.isEmpty then st
    else parseFrom fuel (oneField st)

/-- A refused parse stays refused, and stays put.

    The loop stops at the first refusal, so this is what lets the refinement
    carry only the fact of refusal from that point on. -/
theorem parseFrom_refused (fuel : Nat) (st : ParseState) (h : st.refused = true) :
    parseFrom fuel st = st := by
  cases fuel <;> simp [parseFrom, h]

/-- A parse with nothing left stays put, for the same reason a refused one
    does: both are why the loop stops. -/
theorem parseFrom_stuck (fuel : Nat) (st : ParseState) (h : st.rest.isEmpty = true) :
    parseFrom fuel st = st := by
  cases fuel <;> simp [parseFrom, h]

/-- Running the fold for `n` turns and then `m` more is the same as running it
    for `n + m` at once. What lets a loop's invariant be stated against a fixed
    number of turns *taken*, rather than recomputed against however much fuel
    happens to remain: the answer after `n` steps does not depend on how much
    fuel was left over from a larger budget. -/
theorem parseFrom_add (n m : Nat) (st : ParseState) :
    parseFrom (n + m) st = parseFrom m (parseFrom n st) := by
  induction n generalizing st with
  | zero => simp [parseFrom]
  | succ k ih =>
    by_cases hr : st.refused = true
    · have h1 : parseFrom (k + 1) st = st := parseFrom_refused (k + 1) st hr
      have h2 : parseFrom (k + 1 + m) st = st := parseFrom_refused (k + 1 + m) st hr
      have h3 : parseFrom m st = st := parseFrom_refused m st hr
      rw [h1, h2, h3]
    · by_cases he : st.rest.isEmpty = true
      · have h1 : parseFrom (k + 1) st = st := parseFrom_stuck (k + 1) st he
        have h2 : parseFrom (k + 1 + m) st = st := parseFrom_stuck (k + 1 + m) st he
        have h3 : parseFrom m st = st := parseFrom_stuck m st he
        rw [h1, h2, h3]
      · have hr' : st.refused = false := by simpa using hr
        have he' : st.rest.isEmpty = false := by simpa using he
        have hcond : (st.refused || st.rest.isEmpty) = false := by
          rw [hr', he']; rfl
        have h1 : parseFrom (k + 1) st = parseFrom k (oneField st) := by
          rw [parseFrom]; simp [hcond]
        have h2 : parseFrom (k + 1 + m) st = parseFrom (k + m) (oneField st) := by
          have hk : k + 1 + m = k + m + 1 := by omega
          rw [hk, parseFrom]; simp [hcond]
        rw [h1, h2, ih (oneField st)]

/-- The empty parse over a byte string. -/
def initial (bs : List UInt8) : ParseState :=
  { rest := bs, seen := [], ratchetKey := [], counter := 0, previousCounter := 0,
    ciphertext := [], pq := [], refused := false }

/-- Parse the protobuf region of a ratchet message.

    Three refusals after the loop, and each is a policy rather than a detail.
    Bytes left over mean a sixth field or a truncation. A missing field is
    refused rather than defaulted, because a default is a value nobody sent.
    Field *order* is not among them: the external profile's emitted order is a
    property of the encoder, not of the format. -/
def parseRatchetBody (bs : List UInt8) : Option RatchetBody :=
  if bs.length > maxMessageLen then none
  else
    let st := parseFrom maxFields (initial bs)
    if st.refused then none
    else if !st.rest.isEmpty then none
    else if !(seen st.seen fieldRatchetKey && seen st.seen fieldCounter
              && seen st.seen fieldPreviousCounter && seen st.seen fieldCiphertext
              && seen st.seen fieldPq) then none
    else some { ratchetKey := st.ratchetKey, counter := st.counter,
                previousCounter := st.previousCounter, ciphertext := st.ciphertext,
                pq := st.pq }

/-! ## The prekey envelope profile

Eight fields, numbered as in the external interoperability profile
(`tacenta-spec/CONSTANTS.md`), one of them optional. `prekeyId` is
**the only optional field in either message type**: absent means omitted
entirely, not zero-filled, because a bundle with no one-time prekey produces
a message without the field and it still establishes. The missing-field
check below excludes it for exactly that reason -- the external profile omits
it from well-formed messages, so requiring it would refuse them.

An envelope has no trailing authenticator: the protobuf region runs to the
end, unlike the ratchet message. That is the one difference in
`parsePrekeyBody`'s own shape below, beyond the field count. -/

def fieldPrekeyId : Nat := 1
def fieldBaseKey : Nat := 2
def fieldIdentityKey : Nat := 3
def fieldMessage : Nat := 4
def fieldRegistrationId : Nat := 5
def fieldSignedPrekeyId : Nat := 6
def fieldPqPrekeyId : Nat := 7
def fieldKem : Nat := 8

/-- A parsed prekey envelope. -/
structure PrekeyBody where
  prekeyId : Option Nat
  baseKey : List UInt8
  identityKey : List UInt8
  message : List UInt8
  registrationId : Nat
  signedPrekeyId : Nat
  pqPrekeyId : Nat
  kem : List UInt8
  deriving Repr, DecidableEq, Inhabited

/-- The envelope parse in progress. Nests `body` rather than flattening its
    fields, mirroring the real `EnvelopeParse`'s own shape. -/
structure EnvelopeParseState where
  rest : List UInt8
  seen : List Nat
  body : PrekeyBody
  refused : Bool
  deriving Repr, Inhabited

/-- Read one envelope field into the state.

    Mirrors `one_envelope_field`, including that a refusal leaves the rest of
    the state alone. -/
def oneEnvelopeField (st : EnvelopeParseState) : EnvelopeParseState :=
  match tag st.rest with
  | none => { st with refused := true }
  | some ((field, wire), rest1) =>
    match admit st.seen field with
    | none => { st with rest := rest1, refused := true }
    | some seen1 =>
      let st1 := { st with rest := rest1, seen := seen1 }
      if field == fieldPrekeyId then
        match wire with
        | WireType.varint =>
          match varint rest1 with
          | none => { st1 with refused := true }
          | some (v, rest2) => { st1 with rest := rest2, body := { st1.body with prekeyId := some v } }
        | _ => { st1 with refused := true }
      else if field == fieldBaseKey then
        match wire with
        | WireType.lengthDelimited =>
          match lengthDelimited rest1 with
          | none => { st1 with refused := true }
          | some (v, rest2) => { st1 with rest := rest2, body := { st1.body with baseKey := v } }
        | _ => { st1 with refused := true }
      else if field == fieldIdentityKey then
        match wire with
        | WireType.lengthDelimited =>
          match lengthDelimited rest1 with
          | none => { st1 with refused := true }
          | some (v, rest2) => { st1 with rest := rest2, body := { st1.body with identityKey := v } }
        | _ => { st1 with refused := true }
      else if field == fieldMessage then
        match wire with
        | WireType.lengthDelimited =>
          match lengthDelimited rest1 with
          | none => { st1 with refused := true }
          | some (v, rest2) => { st1 with rest := rest2, body := { st1.body with message := v } }
        | _ => { st1 with refused := true }
      else if field == fieldRegistrationId then
        match wire with
        | WireType.varint =>
          match varint rest1 with
          | none => { st1 with refused := true }
          | some (v, rest2) => { st1 with rest := rest2, body := { st1.body with registrationId := v } }
        | _ => { st1 with refused := true }
      else if field == fieldSignedPrekeyId then
        match wire with
        | WireType.varint =>
          match varint rest1 with
          | none => { st1 with refused := true }
          | some (v, rest2) => { st1 with rest := rest2, body := { st1.body with signedPrekeyId := v } }
        | _ => { st1 with refused := true }
      else if field == fieldPqPrekeyId then
        match wire with
        | WireType.varint =>
          match varint rest1 with
          | none => { st1 with refused := true }
          | some (v, rest2) => { st1 with rest := rest2, body := { st1.body with pqPrekeyId := v } }
        | _ => { st1 with refused := true }
      else if field == fieldKem then
        match wire with
        | WireType.lengthDelimited =>
          match lengthDelimited rest1 with
          | none => { st1 with refused := true }
          | some (v, rest2) => { st1 with rest := rest2, body := { st1.body with kem := v } }
        | _ => { st1 with refused := true }
      else { st1 with refused := true }

/-- Read envelope fields until refusal, exhaustion, or the field bound. Same
    shape as `parseFrom`, over `EnvelopeParseState` rather than `ParseState`:
    kept separate rather than generalizing the two into one, since
    `parseFrom` and its own fixed-point/composition lemmas already ship and
    are depended on, and a shared abstraction bought nothing here that a
    second, small, directly-analogous definition does not already give. -/
def envelopeParseFrom : Nat → EnvelopeParseState → EnvelopeParseState
  | 0, st => st
  | fuel + 1, st =>
    if st.refused || st.rest.isEmpty then st
    else envelopeParseFrom fuel (oneEnvelopeField st)

theorem envelopeParseFrom_refused (fuel : Nat) (st : EnvelopeParseState) (h : st.refused = true) :
    envelopeParseFrom fuel st = st := by
  cases fuel <;> simp [envelopeParseFrom, h]

theorem envelopeParseFrom_stuck (fuel : Nat) (st : EnvelopeParseState) (h : st.rest.isEmpty = true) :
    envelopeParseFrom fuel st = st := by
  cases fuel <;> simp [envelopeParseFrom, h]

theorem envelopeParseFrom_add (n m : Nat) (st : EnvelopeParseState) :
    envelopeParseFrom (n + m) st = envelopeParseFrom m (envelopeParseFrom n st) := by
  induction n generalizing st with
  | zero => simp [envelopeParseFrom]
  | succ k ih =>
    by_cases hr : st.refused = true
    · have h1 : envelopeParseFrom (k + 1) st = st := envelopeParseFrom_refused (k + 1) st hr
      have h2 : envelopeParseFrom (k + 1 + m) st = st := envelopeParseFrom_refused (k + 1 + m) st hr
      have h3 : envelopeParseFrom m st = st := envelopeParseFrom_refused m st hr
      rw [h1, h2, h3]
    · by_cases he : st.rest.isEmpty = true
      · have h1 : envelopeParseFrom (k + 1) st = st := envelopeParseFrom_stuck (k + 1) st he
        have h2 : envelopeParseFrom (k + 1 + m) st = st := envelopeParseFrom_stuck (k + 1 + m) st he
        have h3 : envelopeParseFrom m st = st := envelopeParseFrom_stuck m st he
        rw [h1, h2, h3]
      · have hr' : st.refused = false := by simpa using hr
        have he' : st.rest.isEmpty = false := by simpa using he
        have hcond : (st.refused || st.rest.isEmpty) = false := by
          rw [hr', he']; rfl
        have h1 : envelopeParseFrom (k + 1) st = envelopeParseFrom k (oneEnvelopeField st) := by
          rw [envelopeParseFrom]; simp [hcond]
        have h2 : envelopeParseFrom (k + 1 + m) st = envelopeParseFrom (k + m) (oneEnvelopeField st) := by
          have hk : k + 1 + m = k + m + 1 := by omega
          rw [hk, envelopeParseFrom]; simp [hcond]
        rw [h1, h2, ih (oneEnvelopeField st)]

/-- The empty envelope parse over a byte string. -/
def initialEnvelope (bs : List UInt8) : EnvelopeParseState :=
  { rest := bs, seen := [],
    body := { prekeyId := none, baseKey := [], identityKey := [], message := [],
              registrationId := 0, signedPrekeyId := 0, pqPrekeyId := 0, kem := [] },
    refused := false }

/-- Parse the protobuf region of a prekey envelope.

    Field 1, `prekeyId`, is deliberately absent from the missing-field check:
    the external profile omits it from well-formed messages, so requiring it
    would refuse them. -/
def parsePrekeyBody (bs : List UInt8) : Option PrekeyBody :=
  if bs.length > maxMessageLen then none
  else
    let st := envelopeParseFrom maxFields (initialEnvelope bs)
    if st.refused then none
    else if !st.rest.isEmpty then none
    else if !(seen st.seen fieldBaseKey && seen st.seen fieldIdentityKey
              && seen st.seen fieldMessage && seen st.seen fieldRegistrationId
              && seen st.seen fieldSignedPrekeyId && seen st.seen fieldPqPrekeyId
              && seen st.seen fieldKem) then none
    else some st.body

/-- A length-delimited tag, for building a message by hand below: field number
    and wire type packed the way `decodeTag` reads them back. -/
private def ldTag (field : Nat) : List UInt8 := encodeVarint (field * 8 + 2)

/-- A varint-typed tag, same purpose. -/
private def vTag (field : Nat) : List UInt8 := encodeVarint (field * 8)

/-- Omitting the one optional field does not refuse the message: a bundle
    with a required set of fields but no one-time prekey still parses. -/
example :
    let body : PrekeyBody := { prekeyId := none, baseKey := [1], identityKey := [2], message := [3], registrationId := 7, signedPrekeyId := 8, pqPrekeyId := 9, kem := [4] }
    let bytes := ldTag fieldBaseKey ++ encodeVarint 1 ++ [1]
      ++ ldTag fieldIdentityKey ++ encodeVarint 1 ++ [2]
      ++ ldTag fieldMessage ++ encodeVarint 1 ++ [3]
      ++ vTag fieldRegistrationId ++ encodeVarint 7
      ++ vTag fieldSignedPrekeyId ++ encodeVarint 8
      ++ vTag fieldPqPrekeyId ++ encodeVarint 9
      ++ ldTag fieldKem ++ encodeVarint 1 ++ [4]
    parsePrekeyBody bytes = some body := by native_decide

/-! ## Properties of the model itself

Not refinement -- nothing here mentions the Rust. These are the facts the
refinement proof needs to have in hand about its own specification, and they are
worth stating separately because each is either true of this model or reveals
that the model is not the one intended. -/

/-- Every value this decoder returns fits in the field it is decoded into.

    Needed by item 3 for a reason that is not obvious until the proof asks for
    it. The Rust checks `value + part` at every step, against a running total;
    the model checks suffix totals. Relating the two needs to know that the
    total is bounded, which is what this says, and then monotonicity does the
    rest. -/
theorem varintFrom_bounded (fuel : Nat) :
    ∀ (factor acc : Nat) (bs : List UInt8) (w : Nat) (rest : List UInt8),
    varintFrom fuel factor acc bs = some (w, rest) → w ≤ maxU32 := by
  induction fuel with
  | zero => intro factor acc bs w rest h; simp [varintFrom] at h
  | succ n ih =>
    intro factor acc bs w rest h
    unfold varintFrom at h
    repeat' (split at h <;> simp_all)
    all_goals first
      | omega
      | exact ih _ _ _ _ _ h.2.2
      | exact ih _ _ _ _ _ h.2.2.2

/-- And therefore the entry point's. -/
theorem varint_bounded (bs : List UInt8) (w : Nat) (rest : List UInt8) :
    varint bs = some (w, rest) → w ≤ maxU32 :=
  varintFrom_bounded maxVarintBytes 1 0 bs w rest

/-- No bytes, no varint, at any fuel. The empty-reader case of item 3. -/
theorem varintFrom_nil (fuel factor acc : Nat) : varintFrom fuel factor acc [] = none := by
  cases fuel <;> simp [varintFrom]

/-! ## What is deliberately absent

**Unknown-field skipping.** This profile refuses field numbers above
`maxFieldNumber` rather than skipping them. Skipping is what makes a protobuf
decoder tolerant across schema versions, and tolerance is the wrong default for
a decoder whose output selects ratchet keys: an unknown field is a byte string
whose meaning nobody has defined, and accepting it means accepting that.

The cost is real and is a compatibility risk rather than a security one. If the
external profile gains a field, this profile stops accepting those messages and
says so; compatibility is claimed by version (ADR-0004).

**Duplicate fields.** Not modelled at this level because they are a property
of a message, not of a field, and belong with the message-level parsing that
reads these primitives; the Rust refuses a duplicate field number and bounds
the field count by `MAX_FIELDS` at the message level. -/

/-! ## Why the accumulation is bounded

Without the bound `varintFrom` would compute in `Nat` and return a
thirty-five-bit value that the Rust refuses, so the model would describe a
decoder more permissive than the one that exists.

That is the more dangerous direction of the two. A model stricter than the code
makes the refinement fail loudly; a model looser than the code makes it fail
only for the inputs nobody tried, and in between it licenses a claim -- "these
byte strings are accepted" -- that is false about the shipping decoder.

A disagreement of that kind is visible from the refinement statement, not
from reading either side: T1 never asks, and the examples below have no case
in the range unless one is put there, which is the argument for item 3
stated concretely. -/

/-! ## Known answers

Sampled agreement between this model and the shape it describes, before any
theorem relates it to the Rust. These are cheap and they catch a model that is
wrong on its own terms, which no refinement proof would: a proof that the code
matches a wrong model is a proof of nothing. -/

/-- One byte, below the continuation bit, is itself. -/
example : varint [0x05] = some (5, []) := by native_decide

/-- Two bytes: `0xAC 0x02` is 300, the canonical protobuf example. -/
example : varint [0xAC, 0x02] = some (300, []) := by native_decide

/-- Trailing bytes are returned rather than consumed. -/
example : varint [0x05, 0xFF] = some (5, [0xFF]) := by native_decide

/-- A non-minimal encoding of zero is refused. Two spellings of one value is
    what the minimality rule exists to prevent. -/
example : varint [0x80, 0x00] = none := by native_decide

/-- A varint longer than the profile allows is refused rather than truncated. -/
example : varint [0x80, 0x80, 0x80, 0x80, 0x80, 0x01] = none := by native_decide

/-- The largest value that fits. -/
example : varint [0xFF, 0xFF, 0xFF, 0xFF, 0x0F] = some (maxU32, []) := by native_decide

/-- Five bytes carrying more than thirty-two bits are refused.

    This is the case that separates a model bounded on accumulation from one
    computing in `Nat`; see the note above. -/
example : varint [0xFF, 0xFF, 0xFF, 0xFF, 0x7F] = none := by native_decide

/-- Field 1, wire type 2: the tag byte `0x0A`. -/
example : decodeTag 10 = some (1, WireType.lengthDelimited) := by native_decide

/-- Field 0 does not exist in protobuf and is refused. -/
example : decodeTag 2 = none := by native_decide

/-- A field number above the profile is refused rather than skipped. -/
example : decodeTag ((maxFieldNumber + 1) * 8 + 2) = none := by native_decide

/-- Wire type 5, which this profile does not carry. -/
example : decodeTag 13 = none := by native_decide

/-- A length-delimited field takes exactly its length. -/
example : lengthDelimited [0x03, 0xAA, 0xBB, 0xCC, 0xDD]
    = some ([0xAA, 0xBB, 0xCC], [0xDD]) := by native_decide

/-- A length past the end is refused rather than taking what is there. -/
example : lengthDelimited [0x08, 0xAA] = none := by native_decide

end Model.Protobuf
