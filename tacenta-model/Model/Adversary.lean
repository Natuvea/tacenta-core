/-
Model.Adversary: what an attacker can derive from what it has taken.

This is the piece the four remaining security properties were waiting on, and
the shape of it is the whole design decision, so it is worth stating plainly
before any of it.

## Why keys here are terms and not bytes

Forward secrecy says that an attacker who takes a party's state cannot read the
messages that came before. Everywhere else in this repository a key is a byte
string, and over byte strings that sentence is not provable and not even
properly statable: it reduces to "the chain step cannot be inverted", which is an
assumption about SHA-256 rather than a fact about this protocol. Written over
bytes the theorem would either be circular or false.

So the attacker's world is *symbolic*. A key is a term recording how it was
made -- the chain key three steps along from this secret, the message key of that
chain key -- rather than the bytes it would evaluate to. Two terms are equal when
they were made the same way. A predecessor is then a syntactically different
thing from anything derived forward of it, and "cannot be derived" becomes a
structural claim an induction can settle.

This is the standard move, and it is what the symbolic protocol analysers do. It
is not a weaker claim than a computational one, it is a *different* one, and the
difference is an assumption that has to be stated rather than hidden:

**The fidelity assumption.** A symbolic model says the attacker learns nothing
except by the rules given. Against the real protocol that holds only if the key
derivation really is one-way and collision-resistant, and that is not proved
here, or anywhere in this repository. What the model contributes is that *given*
those primitives, the protocol's own structure leaks nothing -- which is exactly
the part a protocol can get wrong on its own, and exactly what the byte-level
vectors cannot check.

Nothing in this file evaluates a hash. That is the point.
-/

namespace Model.Adversary

/-! ## Terms

A key, as the attacker sees it: a record of how it was derived. The constructors
mirror the model's key schedule one for one, and nothing else may make a key. -/

inductive Sym where
  /-- A secret the protocol started from, from session establishment. Indexed so
      distinct sessions are distinct terms. -/
  | seed (i : Nat)
  /-- A Diffie-Hellman output. Indexed for the same reason. The attacker may
      hold one without holding the private keys behind it. -/
  | dhOut (i : Nat)
  /-- The next chain key: `(kdfCk ck).1`. -/
  | chain (ck : Sym)
  /-- The message key of a chain key: `(kdfCk ck).2`. -/
  | msg (ck : Sym)
  /-- The next root key: `(kdfRk rk dh).1`. -/
  | rootNext (rk dh : Sym)
  /-- The chain key a root step produces: `(kdfRk rk dh).2`. -/
  | chainOf (rk dh : Sym)
  deriving Repr, DecidableEq

/-! ## What the attacker can derive

One rule per way the protocol derives a key, and **no rule that goes backwards**.
That absence is the model's content: it is where one-wayness enters, and it
enters as the shape of an inductive definition rather than as an assumption
buried in a proof. -/

inductive Knows (held : Sym → Prop) : Sym → Prop where
  /-- What it took. -/
  | held {k} : held k → Knows held k
  /-- A chain can always be run forward. -/
  | chain {ck} : Knows held ck → Knows held (.chain ck)
  /-- And a message key read off it. -/
  | msg {ck} : Knows held ck → Knows held (.msg ck)
  /-- A root step needs both the root key and the agreement's output. -/
  | rootNext {rk dh} : Knows held rk → Knows held dh → Knows held (.rootNext rk dh)
  | chainOf {rk dh} : Knows held rk → Knows held dh → Knows held (.chainOf rk dh)

/-! ## Reachability

The structural fact everything else rests on: whatever the attacker derives is
built *out of* something it held. Nothing appears from nowhere, and in particular
nothing appears from below.

`Reaches a b` says `b` can be built from `a` by the rules above -- `a` is at or
beneath `b` in the derivation. -/

inductive Reaches : Sym → Sym → Prop where
  | refl {a} : Reaches a a
  | chain {a b} : Reaches a b → Reaches a (.chain b)
  | msg {a b} : Reaches a b → Reaches a (.msg b)
  | rootL {a b d} : Reaches a b → Reaches a (.rootNext b d)
  | rootR {a b d} : Reaches a d → Reaches a (.rootNext b d)
  | chainOfL {a b d} : Reaches a b → Reaches a (.chainOf b d)
  | chainOfR {a b d} : Reaches a d → Reaches a (.chainOf b d)

/-- Everything the attacker knows is reachable from something it held.

    The bridge between "derived" and "structurally above", and the lemma every
    secrecy statement below will go through: to show a key is *not* derivable, it
    is enough to show it is not above anything taken. -/
theorem knows_reaches {held : Sym → Prop} {k : Sym} (h : Knows held k) :
    ∃ s, held s ∧ Reaches s k := by
  induction h with
  | held hs => exact ⟨_, hs, .refl⟩
  | chain _ ih => obtain ⟨s, hs, hr⟩ := ih; exact ⟨s, hs, .chain hr⟩
  | msg _ ih => obtain ⟨s, hs, hr⟩ := ih; exact ⟨s, hs, .msg hr⟩
  | rootNext _ _ ih _ => obtain ⟨s, hs, hr⟩ := ih; exact ⟨s, hs, .rootL hr⟩
  | chainOf _ _ ih _ => obtain ⟨s, hs, hr⟩ := ih; exact ⟨s, hs, .chainOfL hr⟩

/-! ## Depth

A measure that only grows as a term is built up, so a shorter term cannot be
reachable from a longer one. This is what turns "no rule goes backwards" into an
argument. -/

def depth : Sym → Nat
  | .seed _ => 0
  | .dhOut _ => 0
  | .chain ck => depth ck + 1
  | .msg ck => depth ck + 1
  | .rootNext rk dh => max (depth rk) (depth dh) + 1
  | .chainOf rk dh => max (depth rk) (depth dh) + 1

/-- Reaching never goes down. -/
theorem depth_le_of_reaches {a b : Sym} (h : Reaches a b) : depth a ≤ depth b := by
  induction h with
  | refl => exact Nat.le_refl _
  | chain _ ih => simp only [depth]; omega
  | msg _ ih => simp only [depth]; omega
  | rootL _ ih => simp only [depth]; omega
  | rootR _ ih => simp only [depth]; omega
  | chainOfL _ ih => simp only [depth]; omega
  | chainOfR _ ih => simp only [depth]; omega

/-- The only ways to reach a message key: be it, or reach the chain key under it.

    An inversion lemma, stated over free variables rather than applied inline,
    because eliminating a `Reaches` whose two ends are both concrete asks the
    elaborator to unify more than it can. -/
theorem reaches_msg_inv {a b : Sym} (h : Reaches a (.msg b)) :
    a = .msg b ∨ Reaches a b := by
  cases h with
  | refl => exact Or.inl rfl
  | msg h' => exact Or.inr h'

/-- A leaf is reached only by being it. Agreement outputs and seeds are leaves,
    which is what makes a fresh one unavailable to an attacker that did not take
    it. -/
theorem reaches_dhOut_inv {a : Sym} {i : Nat} (h : Reaches a (.dhOut i)) :
    a = .dhOut i := by
  cases h with
  | refl => rfl

/-- A seed is a leaf, like an agreement output. -/
theorem reaches_seed_inv {a : Sym} {i : Nat} (h : Reaches a (.seed i)) :
    a = .seed i := by
  cases h with
  | refl => rfl

/-- The only ways to reach a chain step: be it, or reach the key under it. -/
theorem reaches_chain_inv {a b : Sym} (h : Reaches a (.chain b)) :
    a = .chain b ∨ Reaches a b := by
  cases h with
  | refl => exact Or.inl rfl
  | chain h' => exact Or.inr h'

/-- Deriving a chain key from a root step needs *both* halves, unless the whole
    thing was taken outright. The rule has two premises and this is that fact
    made usable. -/
theorem knows_chainOf_inv {held : Sym → Prop} {rk dh : Sym}
    (h : Knows held (.chainOf rk dh)) :
    held (.chainOf rk dh) ∨ (Knows held rk ∧ Knows held dh) := by
  cases h with
  | held hh => exact Or.inl hh
  | chainOf h1 h2 => exact Or.inr ⟨h1, h2⟩

/-- The same for the root key a step produces. -/
theorem knows_rootNext_inv {held : Sym → Prop} {rk dh : Sym}
    (h : Knows held (.rootNext rk dh)) :
    held (.rootNext rk dh) ∨ (Knows held rk ∧ Knows held dh) := by
  cases h with
  | held hh => exact Or.inl hh
  | rootNext h1 h2 => exact Or.inr ⟨h1, h2⟩

/-- So an attacker holding one key knows nothing shallower than it.

    The general form of forward secrecy, before any protocol is mentioned: the
    past is *beneath* the present in this order, and knowledge only climbs. -/
theorem not_knows_of_shallower {s k : Sym} (h : depth k < depth s) :
    ¬ Knows (· = s) k := by
  intro hk
  obtain ⟨s', hs', hr⟩ := knows_reaches hk
  subst hs'
  exact absurd (depth_le_of_reaches hr) (by omega)

end Model.Adversary
