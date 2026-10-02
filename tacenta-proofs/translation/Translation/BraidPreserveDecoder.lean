import Translation.BraidT1

/-!
# What the Braid's preservation theorems need to know about an erasure decoder

`BraidPreserve.lean` shows that two bounds are kept by every successful step of the Braid: the
stored ciphertext `ct1` is at most 4096 bytes, and (on the session unit) every erasure decoder the
state holds needs at most `MAX_CODEWORDS` chunks.  Neither bound is kept by itself.  The one step
that makes a `ct1` is `ct1_dec.message()`, whose result is as long as the decoder was sized for, so
`ct1` stays within 4096 bytes only while the decoder holding it is sized for at most 4096 bytes, and
no clause of `ct1_bounded` or `decoders_bounded` says that.  The theorems therefore carry one more
fact about each decoder a state holds, `Good n d`: *every message this decoder can ever return has
at most `n` bytes*, and (on the session unit) `d.needed <= MAX_CODEWORDS`.

This module is the part of that fact that depends on how the decoder is known.  Here the decoder
type is opaque, so `Good n d` is defined through what the decoder can become (`Reach`) and one law
about the real crate is assumed (`NewMsgLen`): a decoder built for `m` bytes never returns a
message longer than `m`.  The session unit translates the decoder with a body, so
`SessionUnitBraidPreserveDecoder.lean` defines `Good` through the decoder's fields and proves the
same four lemmas from the laws `Vec::truncate` returns at most `n` elements and `usize::div_ceil`
has its value.
`BraidPreserve.lean` uses only `Good`, `Laws` and the lemmas below, and the unit copy of it is the
same text.

`BraidPreserveWitness.lean` shows `Laws` has a model: one implementation of the opaque erasure
operations satisfies it together with the three erasure hypotheses `BraidT3` and `BraidT1` already
take.
-/

open Aeneas Aeneas.Std Result
open tacenta_braid

namespace Tacenta.BraidPreserveDecoder

/-- `d'` is a decoder the Braid can hand on from `d`: the Braid only ever adds a chunk to a decoder
or clones it. -/
inductive Reach : tacenta_erasure.Decoder → tacenta_erasure.Decoder → Prop
  | refl (d : tacenta_erasure.Decoder) : Reach d d
  | add {d d' d'' : tacenta_erasure.Decoder} {c : tacenta_erasure.Chunk} {b : Bool} :
      tacenta_erasure.Decoder.add_chunk d c = ok (b, d') → Reach d' d'' → Reach d d''
  | clone {d d' d'' : tacenta_erasure.Decoder} :
      tacenta_erasure.Decoder.Insts.CoreCloneClone.clone d = ok d' → Reach d' d'' → Reach d d''

/-- **Every message this decoder can ever return is at most `n` bytes**, however many chunks it is
given and however often it is cloned. -/
def Good (n : Nat) (d : tacenta_erasure.Decoder) : Prop :=
  ∀ d', Reach d d' → ∀ v, tacenta_erasure.Decoder.message d' = ok (some v) → v.length ≤ n

/-- **The one law about the erasure crate these theorems add**: a decoder `Decoder::new(m)` builds
never returns a message longer than `m`, however many chunks it is given and however often it is
cloned.  The real `Decoder::message` ends in `out.truncate(self.size)`. -/
def NewMsgLen : Prop :=
  ∀ (m : Usize) (d : tacenta_erasure.Decoder), tacenta_erasure.Decoder.new m = ok d →
    Good m.val d

/-- The laws this world needs.  On the session unit this is a different statement
(`SessionUnitBraidPreserveDecoder.Laws`). -/
def Laws : Prop := NewMsgLen

theorem Good.add {n : Nat} {d d' : tacenta_erasure.Decoder} {c : tacenta_erasure.Chunk} {b : Bool}
    (hg : Good n d) (h : tacenta_erasure.Decoder.add_chunk d c = ok (b, d')) : Good n d' :=
  fun d'' hr v hv => hg d'' (Reach.add h hr) v hv

theorem Good.clone {n : Nat} {d d' : tacenta_erasure.Decoder}
    (hg : Good n d) (h : tacenta_erasure.Decoder.Insts.CoreCloneClone.clone d = ok d') :
    Good n d' :=
  fun d'' hr v hv => hg d'' (Reach.clone h hr) v hv

theorem Good.mono {n n' : Nat} {d : tacenta_erasure.Decoder} (hg : Good n d) (h : n ≤ n') :
    Good n' d :=
  fun d' hr v hv => le_trans (hg d' hr v hv) h

/-- A decoder that returns a message returns one within the bound.  The law is not used here: it is
in the statement so that the session unit's version, which needs it, has the same shape. -/
theorem Good.msg (_hl : Laws) {n : Nat} {d : tacenta_erasure.Decoder} {v : alloc.vec.Vec U8}
    (hg : Good n d) (h : tacenta_erasure.Decoder.message d = ok (some v)) : v.length ≤ n :=
  hg d (Reach.refl d) v h

/-- A decoder built for a message of at most `n` bytes, with `n` a small protocol constant, is
good for `n`.  The bound `n ≤ 4128` is the largest size the Braid builds (`CT2_LEN + MAC_LEN`);
the unit statement of the lemma needs it to bound `needed`. -/
theorem Good.new (hl : Laws) {m : Usize} {d : tacenta_erasure.Decoder} {n : Nat}
    (h : tacenta_erasure.Decoder.new m = ok d) (hmn : m.val ≤ n) (_hn : n ≤ 4128) : Good n d :=
  (hl m d h).mono hmn

end Tacenta.BraidPreserveDecoder

/-! ## Axiom pins

This file states definitions and lemmas that carry no axiom pin of their own. -/


/-! ## Definition pins

The definitions that carry the claim.  A change to a clause, a constructor or a law fails the
build while its pin is present; `attest.py` requires each definition pin to exist
(`REQUIRED_STATEMENT_PINS`) and does not read what it says. -/

/--
info: inductive Tacenta.BraidPreserveDecoder.Reach : tacenta_erasure.Decoder → tacenta_erasure.Decoder → Prop
number of parameters: 0
constructors:
Tacenta.BraidPreserveDecoder.Reach.refl : ∀ (d : tacenta_erasure.Decoder), Tacenta.BraidPreserveDecoder.Reach d d
Tacenta.BraidPreserveDecoder.Reach.add : ∀ {d d' d'' : tacenta_erasure.Decoder} {c : tacenta_erasure.Chunk} {b : Bool},
  d.add_chunk c = ok (b, d') → Tacenta.BraidPreserveDecoder.Reach d' d'' → Tacenta.BraidPreserveDecoder.Reach d d''
Tacenta.BraidPreserveDecoder.Reach.clone : ∀ {d d' d'' : tacenta_erasure.Decoder},
  tacenta_erasure.Decoder.Insts.CoreCloneClone.clone d = ok d' →
    Tacenta.BraidPreserveDecoder.Reach d' d'' → Tacenta.BraidPreserveDecoder.Reach d d''
-/
#guard_msgs in
#print Tacenta.BraidPreserveDecoder.Reach

/--
info: def Tacenta.BraidPreserveDecoder.Good : ℕ → tacenta_erasure.Decoder → Prop :=
fun n d =>
  ∀ (d' : tacenta_erasure.Decoder),
    Tacenta.BraidPreserveDecoder.Reach d d' → ∀ (v : alloc.vec.Vec U8), d'.message = ok (some v) → v.length ≤ n
-/
#guard_msgs in
#print Tacenta.BraidPreserveDecoder.Good

/--
info: def Tacenta.BraidPreserveDecoder.NewMsgLen : Prop :=
∀ (m : Usize) (d : tacenta_erasure.Decoder),
  tacenta_erasure.Decoder.new m = ok d → Tacenta.BraidPreserveDecoder.Good (↑m) d
-/
#guard_msgs in
#print Tacenta.BraidPreserveDecoder.NewMsgLen

/--
info: def Tacenta.BraidPreserveDecoder.Laws : Prop :=
Tacenta.BraidPreserveDecoder.NewMsgLen
-/
#guard_msgs in
#print Tacenta.BraidPreserveDecoder.Laws
