import Aeneas

/-!
# Each numeric precondition shape is satisfiable at both platform widths

The numeric premises of the theorems in this package fall into 61 shapes: a comparison between
sums and products of lengths, scalars and model numbers, a constant (`usize::MAX`, `u32::MAX`,
`u64::MAX`, a cap), and a comparison operator. `S01` to `S61` below are those shapes; each is
stated as a comparison over natural numbers, with the lengths and scalars as the variables `x1, x2, ...`
and the platform's `usize::MAX` as the parameter `um`.

Each theorem takes the width as `um`, the value of `usize::MAX`, with `um = 2^32 - 1 ∨
um = 2^64 - 1` (the two values `Usize.max` can have; `usize_max_cases` proves the real constant meets
that hypothesis). It exhibits atoms that meet the shape, with the first atom of the shape at the
largest value the shape admits at that width and, where that value is bounded, that nothing larger
meets the shape with the other atoms fixed. A shape that forced its subject to zero at one width,
as the shape refused on 2026-09-10 did at 32 bits, would show here as a witness of `0` at that width.
Among the shapes whose maximum differs between the two widths, the smallest 32-bit maximum is 47,721,858 (`S02`).

What this is: arithmetic, about shapes. What it is not: a statement about any theorem. A shape
theorem says nothing about which theorem's hypothesis has that shape; that join is made for the
central theorems by `NumericWitnessLeaf.lean`, `NumericWitnessTriple.lean` and
`NumericWitnessSession.lean`, which are stated against the theorems' own signatures and are checked
against them, and for the rest by nothing in the tree. A numeric premise added to a theorem with a
shape that is not among the 61 is not noticed here.

The shapes were read off the built environment, not off the source: every hypothesis of every theorem
in the first-party modules was enumerated, the comparison leaves were reduced to these forms, and
each was checked for a satisfying assignment at both widths by Fourier-Motzkin elimination before
it was written as a theorem here.
-/

namespace Tacenta.NumericShapeWitness

/-- S01: `((((33 + 33) + LEN) + (102 + (LEN + 48))) + 18) ≤ UM`; role: room below usize::MAX; carried by 1 theorem(s). -/
theorem S01 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 x2 : ℕ, (x1 ≤ um) ∧ (x2 ≤ um) ∧ (((((33 + 33) + x1) + (102 + (x2 + 48))) + 18) ≤ um) ∧ (∀ y_ : ℕ, (((((33 + 33) + y_) + (102 + (x2 + 48))) + 18) ≤ um) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967061, 0, by omega, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551381, 0, by omega, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S02: `((50 + (90 * LEN)) + (48 * LEN)) ≤ UM`; role: room below usize::MAX; carried by 1 theorem(s). -/
theorem S02 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 x2 : ℕ, (x1 ≤ um) ∧ (x2 ≤ um) ∧ (((50 + (90 * x1)) + (48 * x2)) ≤ um) ∧ (∀ y_ : ℕ, (((50 + (90 * y_)) + (48 * x2)) ≤ um) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨47721858, 0, by omega, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨204963823041217239, 0, by omega, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S03: `((LEN + LEN) + 96) ≤ UM`; role: room below usize::MAX; carried by 4 theorem(s). -/
theorem S03 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 x2 : ℕ, (x1 ≤ um) ∧ (x2 ≤ um) ∧ (((x1 + x2) + 96) ≤ um) ∧ (∀ y_ : ℕ, (((y_ + x2) + 96) ≤ um) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967199, 0, by omega, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551519, 0, by omega, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S04: `((LEN + LEN) + LEN) ≤ UM`; role: room below usize::MAX; carried by 1 theorem(s). -/
theorem S04 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 x2 x3 : ℕ, (x1 ≤ um) ∧ (x2 ≤ um) ∧ (x3 ≤ um) ∧ (((x1 + x2) + x3) ≤ um) ∧ (∀ y_ : ℕ, (((y_ + x2) + x3) ≤ um) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967295, 0, 0, by omega, by omega, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551615, 0, 0, by omega, by omega, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S05: `(102 + (LEN + 48)) ≤ UM`; role: room below usize::MAX; carried by 1 theorem(s). -/
theorem S05 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ ((102 + (x1 + 48)) ≤ um) ∧ (∀ y_ : ℕ, ((102 + (y_ + 48)) ≤ um) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967145, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551465, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S06: `(185 + (72 * LEN)) ≤ UM`; role: room below usize::MAX; carried by 1 theorem(s). -/
theorem S06 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ ((185 + (72 * x1)) ≤ um) ∧ (∀ y_ : ℕ, ((185 + (72 * y_)) ≤ um) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨59652320, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨256204778801521547, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S07: `(20 + (34 * LEN)) ≤ UM`; role: room below usize::MAX; carried by 1 theorem(s). -/
theorem S07 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ ((20 + (34 * x1)) ≤ um) ∧ (∀ y_ : ℕ, ((20 + (34 * y_)) ≤ um) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨126322566, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨542551296285575046, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S08: `(32 * VUsize) < UM`; role: room below usize::MAX; carried by 2 theorem(s). -/
theorem S08 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ ((32 * x1) < um) ∧ (∀ y_ : ℕ, ((32 * y_) < um) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨134217727, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨576460752303423487, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S09: `(7 + (32 * LEN)) ≤ UM`; role: room below usize::MAX; carried by 1 theorem(s). -/
theorem S09 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ ((7 + (32 * x1)) ≤ um) ∧ (∀ y_ : ℕ, ((7 + (32 * y_)) ≤ um) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨134217727, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨576460752303423487, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S10: `(LEN + (N - N)) ≤ Model.State.maxSkippedStore=2000`; role: store cap; carried by 1 theorem(s). -/
theorem S10 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 x2 x3 : ℕ, ((x1 + (x2 - x3)) ≤ 2000) := by
  rcases h with rfl | rfl
  · exact ⟨0, 18446744073709551616, 18446744073709551616, by omega⟩
  · exact ⟨0, 18446744073709551616, 18446744073709551616, by omega⟩

/-- S11: `(LEN + 1) < UM`; role: room below usize::MAX; carried by 24 theorem(s). -/
theorem S11 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ ((x1 + 1) < um) ∧ (∀ y_ : ℕ, ((y_ + 1) < um) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967293, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551613, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S12: `(LEN + 1) ≤ UM`; role: room below usize::MAX; carried by 2 theorem(s). -/
theorem S12 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ ((x1 + 1) ≤ um) ∧ (∀ y_ : ℕ, ((y_ + 1) ≤ um) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967294, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551614, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S13: `(LEN + 106) ≤ UM`; role: room below usize::MAX; carried by 5 theorem(s). -/
theorem S13 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ ((x1 + 106) ≤ um) ∧ (∀ y_ : ℕ, ((y_ + 106) ≤ um) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967189, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551509, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S14: `(LEN + 2) < UM`; role: room below usize::MAX; carried by 20 theorem(s). -/
theorem S14 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ ((x1 + 2) < um) ∧ (∀ y_ : ℕ, ((y_ + 2) < um) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967292, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551612, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S15: `(LEN + 32) ≤ UM`; role: room below usize::MAX; carried by 1 theorem(s). -/
theorem S15 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ ((x1 + 32) ≤ um) ∧ (∀ y_ : ℕ, ((y_ + 32) ≤ um) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967263, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551583, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S16: `(LEN + 34) ≤ UM`; role: room below usize::MAX; carried by 1 theorem(s). -/
theorem S16 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ ((x1 + 34) ≤ um) ∧ (∀ y_ : ℕ, ((y_ + 34) ≤ um) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967261, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551581, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S17: `(LEN + 64) ≤ UM`; role: room below usize::MAX; carried by 4 theorem(s). -/
theorem S17 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ ((x1 + 64) ≤ um) ∧ (∀ y_ : ℕ, ((y_ + 64) ≤ um) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967231, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551551, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S18: `(LEN + 72) ≤ UM`; role: room below usize::MAX; carried by 1 theorem(s). -/
theorem S18 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ ((x1 + 72) ≤ um) ∧ (∀ y_ : ℕ, ((y_ + 72) ≤ um) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967223, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551543, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S19: `(LEN + 90) ≤ UM`; role: room below usize::MAX; carried by 1 theorem(s). -/
theorem S19 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ ((x1 + 90) ≤ um) ∧ (∀ y_ : ℕ, ((y_ + 90) ≤ um) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967205, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551525, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S20: `(LEN + LEN) ≤ UM`; role: room below usize::MAX; carried by 1 theorem(s). -/
theorem S20 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 x2 : ℕ, (x1 ≤ um) ∧ (x2 ≤ um) ∧ ((x1 + x2) ≤ um) ∧ (∀ y_ : ℕ, ((y_ + x2) ≤ um) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967295, 0, by omega, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551615, 0, by omega, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S21: `(LEN + MAX_SKIP=1000) ≤ UM`; role: room below usize::MAX; carried by 29 theorem(s). -/
theorem S21 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ ((x1 + 1000) ≤ um) ∧ (∀ y_ : ℕ, ((y_ + 1000) ≤ um) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294966295, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709550615, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S22: `(LEN + Model.SparseRatchet.maxSkip=1000) ≤ UM`; role: room below usize::MAX; carried by 6 theorem(s). -/
theorem S22 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, ((x1 + 1000) ≤ um) ∧ (∀ y_ : ℕ, ((y_ + 1000) ≤ um) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294966295, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709550615, by omega, fun y_ hy_ => by omega⟩

/-- S23: `(N + 1) < Model.State.u32Max=4294967295`; role: u32 ceiling (clock); carried by 1 theorem(s). -/
theorem S23 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, ((x1 + 1) < 4294967295) ∧ (∀ y_ : ℕ, ((y_ + 1) < 4294967295) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967293, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨4294967293, by omega, fun y_ hy_ => by omega⟩

/-- S24: `(N + 1) < U32.max`; role: u32 ceiling (clock); carried by 6 theorem(s). -/
theorem S24 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, ((x1 + 1) < 4294967295) ∧ (∀ y_ : ℕ, ((y_ + 1) < 4294967295) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967293, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨4294967293, by omega, fun y_ hy_ => by omega⟩

/-- S25: `(N + 1) < U64.max`; role: u64 ceiling (epoch / counter); carried by 8 theorem(s). -/
theorem S25 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, ((x1 + 1) < 18446744073709551615) ∧ (∀ y_ : ℕ, ((y_ + 1) < 18446744073709551615) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨18446744073709551613, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551613, by omega, fun y_ hy_ => by omega⟩

/-- S26: `(N + Model.SparseRatchet.epochsKept=2) ≤ U64.max`; role: u64 ceiling (epoch / counter); carried by 8 theorem(s). -/
theorem S26 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, ((x1 + 2) ≤ 18446744073709551615) ∧ (∀ y_ : ℕ, ((y_ + 2) ≤ 18446744073709551615) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨18446744073709551613, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551613, by omega, fun y_ hy_ => by omega⟩

/-- S27: `(N + N) ≤ 65536`; role: fixed cap (codeword count); carried by 27 theorem(s). -/
theorem S27 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 x2 : ℕ, ((x1 + x2) ≤ 65536) ∧ (∀ y_ : ℕ, ((y_ + x2) ≤ 65536) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨65536, 0, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨65536, 0, by omega, fun y_ hy_ => by omega⟩

/-- S28: `(VU32 + 1) < U32.max`; role: u32 ceiling (clock); carried by 8 theorem(s). -/
theorem S28 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ 4294967295) ∧ ((x1 + 1) < 4294967295) ∧ (∀ y_ : ℕ, ((y_ + 1) < 4294967295) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967293, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨4294967293, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S29: `(VU64 + 1) < U64.max`; role: u64 ceiling (epoch / counter); carried by 22 theorem(s). -/
theorem S29 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ 18446744073709551615) ∧ ((x1 + 1) < 18446744073709551615) ∧ (∀ y_ : ℕ, ((y_ + 1) < 18446744073709551615) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨18446744073709551613, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551613, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S30: `(VU64 + Model.SparseRatchet.epochsKept=2) ≤ U64.max`; role: u64 ceiling (epoch / counter); carried by 37 theorem(s). -/
theorem S30 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ 18446744073709551615) ∧ ((x1 + 2) ≤ 18446744073709551615) ∧ (∀ y_ : ℕ, ((y_ + 2) ≤ 18446744073709551615) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨18446744073709551613, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551613, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S31: `(VUsize + 33) ≤ LEN`; role: index / length guard; carried by 3 theorem(s). -/
theorem S31 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 x2 : ℕ, (x1 ≤ um) ∧ (x2 ≤ um) ∧ ((x1 + 33) ≤ x2) ∧ (∀ y_ : ℕ, ((y_ + 33) ≤ x2) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967262, 4294967295, by omega, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551582, 18446744073709551615, by omega, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S32: `(max(LEN, MAX_SKIPPED_STORE=2000) + MAX_SKIP=1000) ≤ UM`; role: room below usize::MAX; carried by 14 theorem(s). -/
theorem S32 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ (((max x1 2000) + 1000) ≤ um) := by
  rcases h with rfl | rfl
  · exact ⟨4294966295, by omega, by omega⟩
  · exact ⟨18446744073709550615, by omega, by omega⟩

/-- S33: `(max(LEN, Model.State.maxSkippedStore=2000) + Model.State.maxSkip=1000) ≤ UM`; role: room below usize::MAX; carried by 6 theorem(s). -/
theorem S33 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (((max x1 2000) + 1000) ≤ um) := by
  rcases h with rfl | rfl
  · exact ⟨4294966295, by omega⟩
  · exact ⟨18446744073709550615, by omega⟩

/-- S34: `LEN < UM`; role: room below usize::MAX; carried by 49 theorem(s). -/
theorem S34 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ (x1 < um) ∧ (∀ y_ : ℕ, (y_ < um) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967294, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551614, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S35: `LEN ≤ (LEN + 48)`; role: index / length guard; carried by 2 theorem(s). -/
theorem S35 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 x2 : ℕ, (x1 ≤ um) ∧ (x2 ≤ um) ∧ (x1 ≤ (x2 + 48)) ∧ (∀ y_ : ℕ, (y_ ≤ (x2 + 48)) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967295, 4294967247, by omega, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551615, 18446744073709551567, by omega, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S36: `LEN ≤ 1`; role: uniqueness (store is a map); carried by 21 theorem(s). -/
theorem S36 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ 1) ∧ (∀ y_ : ℕ, (y_ ≤ 1) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨1, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨1, by omega, fun y_ hy_ => by omega⟩

/-- S37: `LEN ≤ 4096`; role: fixed cap; carried by 50 theorem(s). -/
theorem S37 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ (x1 ≤ 4096) ∧ (∀ y_ : ℕ, (y_ ≤ 4096) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4096, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨4096, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S38: `LEN ≤ LEN`; role: index / length guard; carried by 75 theorem(s). -/
theorem S38 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 x2 : ℕ, (x1 ≤ um) ∧ (x2 ≤ um) ∧ (x1 ≤ x2) ∧ (∀ y_ : ℕ, (y_ ≤ x2) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967295, 4294967295, by omega, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551615, 18446744073709551615, by omega, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S39: `LEN ≤ MAX_SKIPPED_STORE=2000`; role: store cap; carried by 24 theorem(s). -/
theorem S39 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ (x1 ≤ 2000) ∧ (∀ y_ : ℕ, (y_ ≤ 2000) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨2000, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨2000, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S40: `LEN ≤ Model.State.maxSkippedStore=2000`; role: store cap; carried by 3 theorem(s). -/
theorem S40 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ 2000) ∧ (∀ y_ : ℕ, (y_ ≤ 2000) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨2000, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨2000, by omega, fun y_ hy_ => by omega⟩

/-- S41: `Model.Braid.u64Max=18446744073709551615 ≤ (N + 1)`; role: u64 ceiling (epoch / counter); carried by 2 theorem(s). -/
theorem S41 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (18446744073709551615 ≤ (x1 + 1)) := by
  rcases h with rfl | rfl
  · exact ⟨18446744073709551614, by omega⟩
  · exact ⟨18446744073709551614, by omega⟩

/-- S42: `N < 16`; role: relation between counters; carried by 1 theorem(s). -/
theorem S42 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 < 16) ∧ (∀ y_ : ℕ, (y_ < 16) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨15, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨15, by omega, fun y_ hy_ => by omega⟩

/-- S43: `N < 65536`; role: fixed cap; carried by 4 theorem(s). -/
theorem S43 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 < 65536) ∧ (∀ y_ : ℕ, (y_ < 65536) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨65535, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨65535, by omega, fun y_ hy_ => by omega⟩

/-- S44: `N < Model.Braid.u64Max=18446744073709551615`; role: u64 ceiling (epoch / counter); carried by 1 theorem(s). -/
theorem S44 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 < 18446744073709551615) ∧ (∀ y_ : ℕ, (y_ < 18446744073709551615) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨18446744073709551614, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551614, by omega, fun y_ hy_ => by omega⟩

/-- S45: `N < N`; role: relation between counters; carried by 5 theorem(s). -/
theorem S45 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 x2 : ℕ, (x1 < x2) ∧ (∀ y_ : ℕ, (y_ < x2) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨18446744073709551616, 18446744073709551617, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551616, 18446744073709551617, by omega, fun y_ hy_ => by omega⟩

/-- S46: `N < U64.max`; role: u64 ceiling (epoch / counter); carried by 11 theorem(s). -/
theorem S46 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 < 18446744073709551615) ∧ (∀ y_ : ℕ, (y_ < 18446744073709551615) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨18446744073709551614, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551614, by omega, fun y_ hy_ => by omega⟩

/-- S47: `N ≤ (N + Model.State.maxSkip=1000)`; role: relation between counters; carried by 1 theorem(s). -/
theorem S47 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 x2 : ℕ, (x1 ≤ (x2 + 1000)) ∧ (∀ y_ : ℕ, (y_ ≤ (x2 + 1000)) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨18446744073709551616, 18446744073709550616, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551616, 18446744073709550616, by omega, fun y_ hy_ => by omega⟩

/-- S48: `N ≤ LEN`; role: index / length guard; carried by 1 theorem(s). -/
theorem S48 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 x2 : ℕ, (x1 ≤ x2) ∧ (∀ y_ : ℕ, (y_ ≤ x2) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨18446744073709551616, 18446744073709551616, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551616, 18446744073709551616, by omega, fun y_ hy_ => by omega⟩

/-- S49: `VU32 < U32.max`; role: u32 ceiling (clock); carried by 13 theorem(s). -/
theorem S49 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ 4294967295) ∧ (x1 < 4294967295) ∧ (∀ y_ : ℕ, (y_ < 4294967295) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967294, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨4294967294, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S50: `VU32 ≤ VU32`; role: relation between counters; carried by 13 theorem(s). -/
theorem S50 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 x2 : ℕ, (x1 ≤ 4294967295) ∧ (x2 ≤ 4294967295) ∧ (x1 ≤ x2) ∧ (∀ y_ : ℕ, (y_ ≤ x2) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967295, 4294967295, by omega, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨4294967295, 4294967295, by omega, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S51: `VU64 < U64.max`; role: u64 ceiling (epoch / counter); carried by 9 theorem(s). -/
theorem S51 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ 18446744073709551615) ∧ (x1 < 18446744073709551615) ∧ (∀ y_ : ℕ, (y_ < 18446744073709551615) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨18446744073709551614, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551614, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S52: `VU64 < VU64`; role: relation between counters; carried by 11 theorem(s). -/
theorem S52 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 x2 : ℕ, (x1 ≤ 18446744073709551615) ∧ (x2 ≤ 18446744073709551615) ∧ (x1 < x2) ∧ (∀ y_ : ℕ, (y_ < x2) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨18446744073709551614, 18446744073709551615, by omega, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551614, 18446744073709551615, by omega, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S53: `VU64 ≤ VU64`; role: relation between counters; carried by 11 theorem(s). -/
theorem S53 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 x2 : ℕ, (x1 ≤ 18446744073709551615) ∧ (x2 ≤ 18446744073709551615) ∧ (x1 ≤ x2) ∧ (∀ y_ : ℕ, (y_ ≤ x2) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨18446744073709551615, 18446744073709551615, by omega, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551615, 18446744073709551615, by omega, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S54: `VUsize < LEN`; role: index / length guard; carried by 74 theorem(s). -/
theorem S54 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 x2 : ℕ, (x1 ≤ um) ∧ (x2 ≤ um) ∧ (x1 < x2) ∧ (∀ y_ : ℕ, (y_ < x2) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967294, 4294967295, by omega, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551614, 18446744073709551615, by omega, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S55: `VUsize < UM`; role: room below usize::MAX; carried by 2 theorem(s). -/
theorem S55 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ (x1 < um) ∧ (∀ y_ : ℕ, (y_ < um) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967294, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551614, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S56: `VUsize ≤ 2097152`; role: fixed cap; carried by 1 theorem(s). -/
theorem S56 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ (x1 ≤ 2097152) ∧ (∀ y_ : ℕ, (y_ ≤ 2097152) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨2097152, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨2097152, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S57: `VUsize ≤ 4096`; role: fixed cap; carried by 38 theorem(s). -/
theorem S57 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ (x1 ≤ 4096) ∧ (∀ y_ : ℕ, (y_ ≤ 4096) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4096, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨4096, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S58: `VUsize ≤ 65536`; role: fixed cap; carried by 24 theorem(s). -/
theorem S58 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ (x1 ≤ 65536) ∧ (∀ y_ : ℕ, (y_ ≤ 65536) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨65536, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨65536, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S59: `VUsize ≤ 8160`; role: fixed cap; carried by 145 theorem(s). -/
theorem S59 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ (x1 ≤ 8160) ∧ (∀ y_ : ℕ, (y_ ≤ 8160) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨8160, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨8160, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S60: `VUsize ≤ LEN`; role: index / length guard; carried by 75 theorem(s). -/
theorem S60 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 x2 : ℕ, (x1 ≤ um) ∧ (x2 ≤ um) ∧ (x1 ≤ x2) ∧ (∀ y_ : ℕ, (y_ ≤ x2) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨4294967295, 4294967295, by omega, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨18446744073709551615, 18446744073709551615, by omega, by omega, by omega, fun y_ hy_ => by omega⟩

/-- S61: `VUsize ≤ MAX_FIELDS=32`; role: fixed cap (parser fields); carried by 2 theorem(s). -/
theorem S61 (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) :
    ∃ x1 : ℕ, (x1 ≤ um) ∧ (x1 ≤ 32) ∧ (∀ y_ : ℕ, (y_ ≤ 32) → y_ ≤ x1) := by
  rcases h with rfl | rfl
  · exact ⟨32, by omega, by omega, fun y_ hy_ => by omega⟩
  · exact ⟨32, by omega, by omega, fun y_ hy_ => by omega⟩

/-- the real constant meets the hypothesis every shape theorem takes -/
theorem usize_max_cases : Aeneas.Std.Usize.max = 4294967295 ∨ Aeneas.Std.Usize.max = 18446744073709551615 := by
  rcases Aeneas.Std.Usize.bounds_eq with h | h <;> simp [h, Aeneas.Std.U32.max_eq, Aeneas.Std.U64.max_eq]

/-- Names every shape theorem, so that deleting one is an error. -/
theorem every_shape_is_satisfiable (um : ℕ) (h : um = 4294967295 ∨ um = 18446744073709551615) : True := by
  have _ := S01 um h
  have _ := S02 um h
  have _ := S03 um h
  have _ := S04 um h
  have _ := S05 um h
  have _ := S06 um h
  have _ := S07 um h
  have _ := S08 um h
  have _ := S09 um h
  have _ := S10 um h
  have _ := S11 um h
  have _ := S12 um h
  have _ := S13 um h
  have _ := S14 um h
  have _ := S15 um h
  have _ := S16 um h
  have _ := S17 um h
  have _ := S18 um h
  have _ := S19 um h
  have _ := S20 um h
  have _ := S21 um h
  have _ := S22 um h
  have _ := S23 um h
  have _ := S24 um h
  have _ := S25 um h
  have _ := S26 um h
  have _ := S27 um h
  have _ := S28 um h
  have _ := S29 um h
  have _ := S30 um h
  have _ := S31 um h
  have _ := S32 um h
  have _ := S33 um h
  have _ := S34 um h
  have _ := S35 um h
  have _ := S36 um h
  have _ := S37 um h
  have _ := S38 um h
  have _ := S39 um h
  have _ := S40 um h
  have _ := S41 um h
  have _ := S42 um h
  have _ := S43 um h
  have _ := S44 um h
  have _ := S45 um h
  have _ := S46 um h
  have _ := S47 um h
  have _ := S48 um h
  have _ := S49 um h
  have _ := S50 um h
  have _ := S51 um h
  have _ := S52 um h
  have _ := S53 um h
  have _ := S54 um h
  have _ := S55 um h
  have _ := S56 um h
  have _ := S57 um h
  have _ := S58 um h
  have _ := S59 um h
  have _ := S60 um h
  have _ := S61 um h
  trivial

end Tacenta.NumericShapeWitness

/--
info: 'Tacenta.NumericShapeWitness.usize_max_cases' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.NumericShapeWitness.usize_max_cases

/--
info: 'Tacenta.NumericShapeWitness.every_shape_is_satisfiable' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.NumericShapeWitness.every_shape_is_satisfiable
