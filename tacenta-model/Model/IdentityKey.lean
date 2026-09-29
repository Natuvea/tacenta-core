/-
Model.IdentityKey: the identity-key rule, as a Boolean function of 32 bytes.

Written from tacenta-spec/protocol/identities-and-devices.md, "Accepting a
signed statement", check 6, and from the curve's definition in RFC 8032,
section 5.1 (the curve, the base point, the extended-coordinate addition of
section 5.1.4 and the square root of section 5.1.3). It is written from the
page and the RFC, not from `tacenta-core` and not from any library, so that it
can disagree with them.

**The rule.** An identity key is a 32-byte string `u` that
1. is a canonical curve public key (message-format.md, Curve public keys): bit
   255 is clear and the value is below `p = 2^255 - 19`;
2. is not `p - 1`, and `y = (u - 1) / (u + 1) mod p` is the y-coordinate of a
   point `P` of edwards25519, `-x^2 + y^2 = 1 + d x^2 y^2` with
   `d = -121665 / 121666`;
3. has `q * P` equal to the identity, where `q` is the order of the base point
   (identities-and-devices.md, Signing). The two points with that y-coordinate
   give the same answer, so the sign of `x` does not matter and the root that
   the square-root routine returns is used.

A key an honest device publishes is the X25519 public key of a clamped secret,
which is `k * B` for the base point `B` (identities-and-devices.md, The identity
key's secret), so it passes.

**What is and is not established here.** `valid` is a definition to run, and
nothing in this module proves that it computes the rule. Its verdicts are
pinned by the generated vectors (`vectors/identity/identity-key.json`), one per
row of a table whose expected class comes from a separate program that does not
share this code, and by the differential harness (`Difftest.lean`, the request
`identity-key`). The module states no theorem about the curve, and the
lifecycle model does not compute this function: it takes the verdict from an
oracle bit, `Model.Lifecycle.Oracle.identityValid`, which the refinement binds
to the translated Rust. The persisted-state readers do compute it
(`Model.PersistedState`).

The arithmetic is on natural numbers reduced modulo `p`, with a fuel argument
in place of well-founded recursion so that the definitions unfold in the
kernel. Fuel 256 covers every exponent and scalar used below, all under
`2^256`.
-/
import Model.Messages

namespace Model.IdentityKey

open Model.Messages (canonicalKey curveP leValue)

/-! ## The field -/

/-- The prime of the field, `2^255 - 19` (RFC 8032, section 5.1). -/
abbrev p : Nat := curveP

/-- `b ^ e mod p` by squaring, least significant bit first, over at most `fuel`
    bits of `e`. -/
def powModAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, b, e, acc =>
      if e = 0 then acc
      else powModAux fuel (b * b % p) (e / 2) (if e % 2 = 1 then acc * b % p else acc)

/-- `b ^ e mod p` for `e` below `2^256`. -/
def powMod (b e : Nat) : Nat := powModAux 256 (b % p) e 1

/-- The inverse of a nonzero element, by Fermat's little theorem; `0` for `0`. -/
def inv (a : Nat) : Nat := powMod a (p - 2)

/-- A square root of `-1` modulo `p`: `2^((p - 1) / 4)`. -/
def sqrtMinusOne : Nat := powMod 2 ((p - 1) / 4)

/-- A square root of `x` modulo `p` when there is one, by the method of RFC 8032,
    section 5.1.3: the candidate `x^((p + 3) / 8)`, corrected by `sqrt(-1)` when
    its square is `-x`. `p` is 5 modulo 8, so that covers every square. -/
def sqrt? (x : Nat) : Option Nat :=
  let x := x % p
  let r := powMod x ((p + 3) / 8)
  if r * r % p = x then some r
  else
    let r' := r * sqrtMinusOne % p
    if r' * r' % p = x then some r' else none

/-! ## The curve -/

/-- The curve constant `d = -121665 / 121666` (RFC 8032, section 5.1). -/
def curveD : Nat := (p - 121665 * inv 121666 % p) % p

/-- The order `q` of the base point, and of the prime-order subgroup
    (RFC 8032, section 5.1). -/
def subgroupOrder : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

/-- A point in extended coordinates `(X : Y : Z : T)`, with `x = X / Z`,
    `y = Y / Z` and `T = X Y / Z` (RFC 8032, section 5.1.4). -/
structure Point where
  x : Nat
  y : Nat
  z : Nat
  t : Nat
  deriving Repr, DecidableEq

/-- The neutral element, the point `(0, 1)`. -/
def identityPoint : Point := { x := 0, y := 1, z := 1, t := 0 }

/-- Whether a point is the neutral element: `X = 0` and `Y = Z`. (The point
    `(0, -1)` has `X = 0` too and is of order 2, not the neutral element.) -/
def isIdentity (pt : Point) : Bool :=
  pt.x % p == 0 && pt.y % p == pt.z % p

/-- The sum of two points by the unified addition of RFC 8032, section 5.1.4,
    which is complete on this curve: it needs no case for equal, opposite or
    neutral operands. -/
def add (pt qt : Point) : Point :=
  let a := (pt.y + p - pt.x) % p * ((qt.y + p - qt.x) % p) % p
  let b := (pt.y + pt.x) % p * ((qt.y + qt.x) % p) % p
  let c := pt.t * (2 * curveD % p) % p * qt.t % p
  let dd := pt.z * 2 % p * qt.z % p
  let e := (b + p - a) % p
  let f := (dd + p - c) % p
  let g := (dd + c) % p
  let h := (b + a) % p
  { x := e * f % p, y := g * h % p, z := f * g % p, t := e * h % p }

/-- `k * pt` by double-and-add, least significant bit first, over at most `fuel`
    bits of `k`. -/
def mulAux : Nat → Nat → Point → Point → Point
  | 0, _, _, acc => acc
  | fuel + 1, k, base, acc =>
      if k = 0 then acc
      else mulAux fuel (k / 2) (add base base) (if k % 2 = 1 then add acc base else acc)

/-- `k * pt` for `k` below `2^256`. -/
def mul (k : Nat) (pt : Point) : Point := mulAux 256 k pt identityPoint

/-- A point with the given y-coordinate, when there is one. From the curve
    equation, `x^2 = (y^2 - 1) / (d y^2 + 1)`; the denominator is never zero
    because `d` is not a square. Of the two roots, the one `sqrt?` returns. -/
def pointOfY? (y : Nat) : Option Point :=
  let y := y % p
  let num := (y * y % p + p - 1) % p
  let den := (curveD * (y * y % p) % p + 1) % p
  match sqrt? (num * inv den % p) with
  | none => none
  | some x => some { x, y, z := 1, t := x * y % p }

/-! ## The rule -/

/-- Steps 2 and 3 of the rule, for the value `u` of a canonical key: `u` is not
    `p - 1`, `y = (u - 1) / (u + 1) mod p` is the y-coordinate of a point `P`,
    and `q * P` is the neutral element. -/
def inPrimeOrderSubgroup (u : Nat) : Bool :=
  u != p - 1 &&
    match pointOfY? ((u + p - 1) % p * inv ((u + 1) % p) % p) with
    | none => false
    | some pt => isIdentity (mul subgroupOrder pt)

/-- The identity-key rule of identities-and-devices.md, "Accepting a signed
    statement", check 6, for a byte string. A string that is not 32 bytes is
    not a key. The steps follow the page in order: the canonical encoding, then
    `u ≠ p - 1` with `y` the y-coordinate of a point, then `q * P` the neutral
    element. -/
def valid (key : List UInt8) : Bool :=
  key.length == 32 && canonicalKey key && inPrimeOrderSubgroup (leValue key)

/-! ## Build-time checks

A few verdicts, checked by the kernel when this module builds (`decide +kernel`
uses no axiom). They are examples, not a proof that `valid` computes the rule:
the rule's verdicts on the whole table are pinned by the generated vectors. -/

/-- An X25519 public key of a clamped secret. -/
example : valid [0xa4, 0xe0, 0x92, 0x92, 0xb6, 0x51, 0xc2, 0x78, 0xb9, 0x77, 0x2c, 0x56, 0x9f, 0x5f, 0xa9, 0xbb, 0x13, 0xd9, 0x06, 0xb4, 0x6a, 0xb6, 0x8c, 0x9d, 0xf9, 0xdc, 0x2b, 0x44, 0x09, 0xf8, 0xa2, 0x09] = true := by decide +kernel

/-- RFC 7748, section 6.1, Alice's public key. -/
example : valid [0x85, 0x20, 0xf0, 0x09, 0x89, 0x30, 0xa7, 0x54, 0x74, 0x8b, 0x7d, 0xdc, 0xb4, 0x3e, 0xf7, 0x5a, 0x0d, 0xbf, 0x3a, 0x0d, 0x26, 0x38, 0x1a, 0xf4, 0xeb, 0xa4, 0xa9, 0x8e, 0xaa, 0x9b, 0x4e, 0x6a] = true := by decide +kernel

/-- The base point, u = 9. -/
example : valid [0x09, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] = true := by decide +kernel

/-- The sum of an honest key's point and a point of order 8. -/
example : valid [0x03, 0x7f, 0xaa, 0x3b, 0xbf, 0xc6, 0x76, 0xb2, 0x6f, 0x87, 0xfb, 0x14, 0x49, 0xa1, 0x52, 0xbc, 0xb3, 0xeb, 0x7c, 0xfe, 0xee, 0xdb, 0xaa, 0x36, 0x04, 0xde, 0xca, 0x93, 0xac, 0x75, 0x30, 0x4b] = false := by decide +kernel

/-- The sum of an honest key's point and a point of order 2. -/
example : valid [0xcc, 0x80, 0xc6, 0x79, 0x24, 0xdf, 0x11, 0x22, 0x5b, 0xaa, 0x5f, 0xf7, 0x83, 0x8b, 0x65, 0xef, 0x47, 0x47, 0xfc, 0x51, 0x4b, 0x11, 0xa8, 0x10, 0xfb, 0x95, 0x11, 0x06, 0xab, 0x3d, 0x62, 0x0a] = false := by decide +kernel

/-- u = 0, a point of order 2. -/
example : valid [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] = false := by decide +kernel

/-- u = 1, a point of order 4. -/
example : valid [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] = false := by decide +kernel

/-- A u-coordinate of order eight. -/
example : valid [0xe0, 0xeb, 0x7a, 0x7c, 0x3b, 0x41, 0xb8, 0xae, 0x16, 0x56, 0xe3, 0xfa, 0xf1, 0x9f, 0xc4, 0x6a, 0xda, 0x09, 0x8d, 0xeb, 0x9c, 0x32, 0xb1, 0xfd, 0x86, 0x62, 0x05, 0x16, 0x5f, 0x49, 0xb8, 0x00] = false := by decide +kernel

/-- The other u-coordinate of order eight. -/
example : valid [0x5f, 0x9c, 0x95, 0xbc, 0xa3, 0x50, 0x8c, 0x24, 0xb1, 0xd0, 0xb1, 0x55, 0x9c, 0x83, 0xef, 0x5b, 0x04, 0x44, 0x5c, 0xc4, 0x58, 0x1c, 0x8e, 0x86, 0xd8, 0x22, 0x4e, 0xdd, 0xd0, 0x9f, 0x11, 0x57] = false := by decide +kernel

/-- u = p - 1. -/
example : valid [0xec, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f] = false := by decide +kernel

/-- u = 2, on the quadratic twist. -/
example : valid [0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] = false := by decide +kernel

/-- u = p. -/
example : valid [0xed, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f] = false := by decide +kernel

/-- u = 9 with bit 255 set. -/
example : valid [0x09, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80] = false := by decide +kernel

/-- The key 9 spelled as `9 + p`, which reduces to the base point's u but is not
    its canonical spelling. -/
example : valid [0xf6, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f] = false := by decide +kernel

/-- A string that is not 32 bytes is not a key, whatever its value: the base
    point's u cut short or with a byte appended. -/
example : valid [9] = false := by decide +kernel

example : valid (9 :: List.replicate 32 0) = false := by decide +kernel

end Model.IdentityKey
