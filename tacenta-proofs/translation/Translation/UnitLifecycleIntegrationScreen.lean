import Translation.DispatchEvidenceVacuity

/-!
# Screening the hypotheses the session contract integration adds

The integration of the session contract branch into `UnitLifecycleT3.lean` and
`UnitLifecycleInitialDispatch.lean` changes the oracle record `OracleOf` (a conditional KEM success
clause, a pre-draw refusal clause, two draws for signing) and adds evidence records to the dispatch
layer. A theorem whose hypothesis nothing satisfies is true and says nothing, so this module
decides some of the new and changed hypotheses. The results are about hypotheses, not about the
product.

## What is shown

* **A. The concrete branch evidence is empty.** `InitialRatchetConcreteBranchEvidence.randomDraw`
  asks that every RNG state, not only the run's, has a trace with a head, as soon as one inner
  message decodes to a composite whose first agreement succeeds. With `OracleOf.random32`, which
  turns a state whose trace has a head into a state whose trace is the tail, that makes the trace
  of every state longer than every number (`concreteBranchEvidence_empty`). The two end-to-end
  evidence records that contain it are empty under the same premises
  (`endToEndEvidence_empty`, `agreementEndToEndEvidence_empty`).
* **B. Draw counts.** `byteRng` is a byte-stream random source (a list of bytes read from the
  front) and `byteTrace` reads it as 32-byte draws. At that source the translated `random_secret`
  meets the `random32` clause (`byte_random32`). Under `SignFillsOnce64Of`, a law that a signing
  function fills one 64-byte buffer and touches the RNG nowhere else, the two-draw `sigSign` clause
  holds (`sigSignClause_of_law`); under `KemShapeOf`, a law that encapsulation refuses an invalid
  key before it draws and otherwise fills one 32-byte buffer, the three KEM clauses hold
  (`kemClauses_of_law`). `changed_rng_clauses_have_a_model` gives one assignment of the two
  functions that meets both laws with a key the KEM refuses, so the changed clauses are met
  together with `random32` and are not met only by an oracle that never refuses.
  `changed_rng_clauses_of_laws` is the same derivation at the shipped constants.
* **B'. The Braid's key generation.** `BraidSendTraceAgreement`, a hypothesis of
  `public_session_encrypt_of_send_contracts`, asks a Braid send from `KeysUnsampled` to consume one
  trace entry, while the shipped `IncrementalKeyPair::generate` fills a 64-byte seed
  (`tacenta-core/kem/src/lib.rs`, `KEY_GENERATION_SEED_LEN`). Under `SignFillsOnce64` and
  `GenerateFillsOnce64` (one 64-byte fill each), the agreement contradicts `OracleOf.sigSign` at
  any such send whose trace has two entries (`braidSendTrace_conflicts_with_sigSign`): the same
  64-byte fill cannot leave one draw and two draws behind.
* **C. Numeric state records.** `RetryReceiveBounds`, `GeneratedTripleRefusalConditions` and
  `GeneratedTripleSuccessConditions` hold at the model's initial Triple state
  (`retryReceiveBounds_initAlice` and the two `_initAlice` results), and the first is not true of
  every state (`retryReceiveBounds_not_trivial`).

## The sense of the laws

`SignFillsOnce64Of`, `GenerateFillsOnce64Of` and `KemShapeOf` are stated of a function argument, so
each says what one function does. At the shipped constants (`SignFillsOnce64`,
`GenerateFillsOnce64`, `KemShapeOf (@tacenta_boundary.kem.encapsulate)`) they are assumptions about
opaque declarations of the unit, read from `tacenta-core/boundary/src/xeddsa.rs` (`sign`),
`tacenta-core/kem/src/lib.rs` (`IncrementalKeyPair::generate`) and
`tacenta-core/boundary/src/kem.rs` (`encapsulate`), and no theorem here proves them. The model
results show they are not contradictory. Result A uses no law.

**Platform width.** No proof case-splits on the width of `usize`. The only fact used about
`Usize.max` is that it is at least `2^32 - 1` (`Tacenta.SessionUnitSessionT1.small_le_usize_max`),
which holds at both widths, so every result holds for both.

## What this does not show

That `OracleOf` as a whole is satisfiable: its `dh`, `aead`, `kemDecapsulate`, `sigVerify` and
`identityValid` clauses are not decided here. That the shipped functions meet the three laws. That
any dispatch theorem is non-vacuous. Result A needs one inner message whose first agreement
succeeds; every run that gets past the first agreement supplies one. Result B' needs a Braid send
from `KeysUnsampled` with two trace entries left.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3

namespace Tacenta.UnitLifecycleIntegrationScreen

/-! ## A. The concrete branch evidence is empty -/

/-- `InitialRatchetConcreteBranchEvidence.randomDraw` quantifies over every RNG state. With
`OracleOf.random32` it has no term once one inner message decodes to a composite whose first
agreement succeeds. -/
theorem concreteBranchEvidence_empty
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {kem : KemView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    (oracleOf : OracleOf rc crc dh kem trace oracle)
    (message : Slice Std.U8) (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes)
    (dhOutRecv : Model.Lifecycle.Key)
    (hdecode : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .ok (composite, ciphertext))
    (hagree : oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv)
    (rng : R)
    (evidence : InitialRatchetConcreteBranchEvidence (rc := rc) (crc := crc) (trace := trace)
      (dh := dh) (K := K) (view := view) (oracle := oracle) (real := real) (model := model)) :
    False := by
  have key : ∀ n (r : R), n ≤ (trace r).length := by
    intro n
    induction n with
    | zero => intro r; exact Nat.zero_le _
    | succ n ih =>
      intro r
      obtain ⟨draw, rest, hr⟩ := evidence.randomDraw (innerMessage := message) (innerRng := r)
        composite ciphertext dhOutRecv hdecode hagree
      obtain ⟨_, r', _, _, hr'⟩ := oracleOf.random32 r draw rest hr
      have := ih r'
      rw [hr'] at this
      rw [hr, List.length_cons]
      omega
  have := key ((trace rng).length + 1) rng
  omega

/-- The end-to-end evidence of the accepted initial route contains the concrete branch evidence,
so it is empty under the same premises. -/
theorem endToEndEvidence_empty
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {kem : KemView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    (oracleOf : OracleOf rc crc dh kem trace oracle)
    (message : Slice Std.U8) (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes)
    (dhOutRecv : Model.Lifecycle.Key)
    (hdecode : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .ok (composite, ciphertext))
    (hagree : oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv)
    (outerMessage : Slice Std.U8) (rng : R)
    (evidence : InitialRatchetEndToEndEvidence (rc := rc) (crc := crc) (trace := trace)
      (dh := dh) (K := K) (view := view) (oracle := oracle) (real := real) (model := model)
      outerMessage rng) :
    False :=
  concreteBranchEvidence_empty oracleOf message composite ciphertext dhOutRecv hdecode hagree rng
    evidence.concrete

/-- Likewise for the agreement-class route. -/
theorem agreementEndToEndEvidence_empty
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {kem : KemView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    (oracleOf : OracleOf rc crc dh kem trace oracle)
    (message : Slice Std.U8) (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes)
    (dhOutRecv : Model.Lifecycle.Key)
    (hdecode : Model.CompositeHeader.decodeDetailed (sliceOf message) =
      .ok (composite, ciphertext))
    (hagree : oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv)
    (outerMessage : Slice Std.U8) (rng : R)
    (evidence : InitialAgreementRatchetEndToEndEvidence (rc := rc) (crc := crc) (trace := trace)
      (dh := dh) (K := K) (view := view) (oracle := oracle) (real := real) (model := model)
      outerMessage rng) :
    False :=
  concreteBranchEvidence_empty oracleOf message composite ciphertext dhOutRecv hdecode hagree rng
    evidence.concrete

/-! ## B. Draw counts at a byte-stream source -/

/-- A slice of `n` zero bytes, `n` below `2^32`, so it is a slice at both platform widths. -/
def zeroSlice (n : Nat) (h : n ≤ 4294967295) : Slice Std.U8 :=
  ⟨List.replicate n 0#u8, by
    simp only [List.length_replicate]
    exact Tacenta.SessionUnitSessionT1.small_le_usize_max h⟩

def zeros32 : Slice Std.U8 := zeroSlice 32 (by decide)
def zeros64 : Slice Std.U8 := zeroSlice 64 (by decide)

/-- A byte-stream random source: the state is the list of bytes still to be read, and a fill of
`n` bytes reads the first `n`. -/
def byteRng : rand_core_1.RngCore (List Std.U8) where
  next_u32 := fun r => ok (0#u32, r)
  next_u64 := fun r => ok (0#u64, r)
  fill_bytes := fun r buf => ok (r.drop buf.val.length, ⟨r.take buf.val.length, by
    have := buf.property
    simp only [List.length_take]
    omega⟩)
  try_fill_bytes := fun r buf => ok (.Ok (), r, buf)

def byteCrc : rand_core_1.CryptoRng (List Std.U8) := ⟨⟩

/-- The bytes of a list, cut into 32-byte draws; a tail shorter than 32 bytes is not a draw.
Not compiled, so no recursion helper is generated for it. -/
noncomputable def chunks32 (l : List UInt8) : List Model.Lifecycle.Key :=
  if 32 ≤ l.length then l.take 32 :: chunks32 (l.drop 32) else []
termination_by l.length
decreasing_by simp only [List.length_drop]; omega

/-- The draws a byte-stream state holds. -/
noncomputable def byteTrace (r : List Std.U8) : List Model.Lifecycle.Key :=
  chunks32 (r.map Tacenta.SessionUnitBraidT3.u8)

theorem chunks32_eq_cons {l : List UInt8} {d : Model.Lifecycle.Key}
    {rest : List Model.Lifecycle.Key} (h : chunks32 l = d :: rest) :
    32 ≤ l.length ∧ d = l.take 32 ∧ rest = chunks32 (l.drop 32) := by
  rw [chunks32] at h
  split at h
  · simp only [List.cons.injEq] at h
    exact ⟨by assumption, h.1.symm, h.2.symm⟩
  · simp at h

/-- A 32-byte fill reads one draw. -/
theorem byte_fill_32 {r : List Std.U8} {d : Model.Lifecycle.Key}
    {rest : List Model.Lifecycle.Key} (h : byteTrace r = d :: rest) :
    ∃ s, byteRng.fill_bytes r zeros32 = ok (r.drop 32, s) ∧
      byteTrace (r.drop 32) = rest ∧ sliceOf s = d ∧ s.val = r.take 32 := by
  obtain ⟨hlen, hd, hrest⟩ := chunks32_eq_cons h
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp only [byteTrace, List.map_drop, hrest]
  · simp only [sliceOf, zeros32, zeroSlice, List.length_replicate, hd, List.map_take]
  · simp [zeros32, zeroSlice]

/-- A 64-byte fill reads two draws. -/
theorem byte_fill_64 {r : List Std.U8} {d1 d2 : Model.Lifecycle.Key}
    {rest : List Model.Lifecycle.Key} (h : byteTrace r = d1 :: d2 :: rest) :
    ∃ s, byteRng.fill_bytes r zeros64 = ok (r.drop 64, s) ∧
      byteTrace (r.drop 64) = rest ∧ sliceOf s = d1 ++ d2 := by
  obtain ⟨hlen1, hd1, hrest1⟩ := chunks32_eq_cons h
  obtain ⟨hlen2, hd2, hrest2⟩ := chunks32_eq_cons hrest1.symm
  refine ⟨_, rfl, ?_, ?_⟩
  · simp only [byteTrace, List.map_drop]
    rw [hrest2, List.drop_drop]
  · simp only [sliceOf, zeros64, zeroSlice, List.length_replicate, hd1, hd2, List.map_take]
    rw [show (64 : Nat) = 32 + 32 from rfl, List.take_add]

/-- At the byte-stream source the translated `random_secret` meets the `random32` clause of
`OracleOf`: it reads one draw. -/
theorem byte_random32 (crc : rand_core_1.CryptoRng (List Std.U8)) (rng : List Std.U8)
    (draw : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key)
    (h : byteTrace rng = draw :: rest) :
    ∃ value rng', lifecycle.random_secret byteRng crc rng = ok (value, rng') ∧
      arrayOf value = draw ∧ byteTrace rng' = rest := by
  obtain ⟨hlen, hd, hrest⟩ := chunks32_eq_cons h
  have hlen' : 32 ≤ rng.length := by simpa using hlen
  refine ⟨_, _, rfl, ?_, ?_⟩
  · have hL : (↑(Array.repeat 32#usize 0#u8).to_slice : List Std.U8).length = 32 := by
      simp [Array.to_slice, Array.repeat]
    have hT : (List.take 32 rng).length = (32#usize : Std.Usize).val := by
      simp only [List.length_take]; simp; omega
    simp only [hL]
    rw [arrayOf, Array.from_slice_val _ _ hT, hd, List.map_take]
  · have hL : (↑(Array.repeat 32#usize 0#u8).to_slice : List Std.U8).length = 32 := by
      simp [Array.to_slice, Array.repeat]
    simp only [hL, byteTrace, List.map_drop, hrest]

/-! ### The three changed clauses, stated of a function argument

Each definition is the corresponding field of `OracleOf` with the shipped constant replaced by an
argument; the three `_of_oracleOf` results check that the fields have exactly these shapes. -/

def Random32Clause {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) : Prop :=
  ∀ rng draw rest, trace rng = draw :: rest →
    ∃ value rng', lifecycle.random_secret rc crc rng = ok (value, rng') ∧
      arrayOf value = draw ∧ trace rng' = rest

def SigSignClause {R : Type}
    (sign : Array Std.U8 32#usize → Slice Std.U8 → R → Result (Array Std.U8 64#usize × R))
    (trace : R → List Model.Lifecycle.Key) (oracle : Model.Lifecycle.Oracle) : Prop :=
  ∀ secret message rng draw1 draw2 rest, trace rng = draw1 :: draw2 :: rest →
    ∃ signature rng', sign secret message rng = ok (signature, rng') ∧
      trace rng' = rest ∧
      arrayOf signature = oracle.sigSign (arrayOf secret) (sliceOf message) draw1 draw2

def KemClauses {R : Type}
    (encap : Slice Std.U8 → R → Result (core.result.Result
      (alloc.vec.Vec Std.U8 × Array Std.U8 32#usize) tacenta_boundary.kem.KemError × R))
    (trace : R → List Model.Lifecycle.Key) (oracle : Model.Lifecycle.Oracle) : Prop :=
  (∀ publicKey rng draw rest expected,
    trace rng = draw :: rest →
    oracle.kemEncaps (sliceOf publicKey) draw = some expected →
    ∃ result rng', encap publicKey rng = ok (.Ok result, rng') ∧
      trace rng' = rest ∧ encapsulationOf (.Ok result) = some expected) ∧
  (∀ publicKey rng error,
    oracle.kemValid (sliceOf publicKey) = false →
    encap publicKey rng = ok (.Err error, rng)) ∧
  (∀ publicKey rng error,
    encap publicKey rng = ok (.Err error, rng) →
    oracle.kemValid (sliceOf publicKey) = false ∧
    ∀ draw, oracle.kemEncaps (sliceOf publicKey) draw = none)

theorem random32Clause_of_oracleOf {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView}
    {kem : KemView} {oracle : Model.Lifecycle.Oracle}
    (oracleOf : OracleOf rc crc dh kem trace oracle) : Random32Clause rc crc trace :=
  oracleOf.random32

theorem sigSignClause_of_oracleOf {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView}
    {kem : KemView} {oracle : Model.Lifecycle.Oracle}
    (oracleOf : OracleOf rc crc dh kem trace oracle) :
    SigSignClause (tacenta_boundary.xeddsa.sign rc crc) trace oracle :=
  oracleOf.sigSign

theorem kemClauses_of_oracleOf {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView}
    {kem : KemView} {oracle : Model.Lifecycle.Oracle}
    (oracleOf : OracleOf rc crc dh kem trace oracle) :
    KemClauses (tacenta_boundary.kem.encapsulate rc crc) trace oracle :=
  ⟨oracleOf.kemEncapsulateSuccess, oracleOf.kemInvalidKey, oracleOf.kemEncapsulateError⟩

theorem byte_random32Clause : Random32Clause byteRng byteCrc byteTrace :=
  byte_random32 byteCrc

/-! ### The laws -/

/-- The type of `tacenta_boundary.xeddsa.sign`. -/
abbrev SignFn := ∀ {R : Type}, rand_core_1.RngCore R → rand_core_1.CryptoRng R →
  Array Std.U8 32#usize → Slice Std.U8 → R → Result (Array Std.U8 64#usize × R)

/-- The type of `tacenta_kem.IncrementalKeyPair.generate`. -/
abbrev GenerateFn := ∀ {R : Type}, rand_core_1.RngCore R → rand_core_1.CryptoRng R →
  R → Result (core.result.Result tacenta_kem.IncrementalKeyPair tacenta_kem.KemError × R)

/-- The type of `tacenta_boundary.kem.encapsulate`. -/
abbrev EncapFn := ∀ {R : Type}, rand_core_1.RngCore R → rand_core_1.CryptoRng R →
  Slice Std.U8 → R → Result (core.result.Result
    (alloc.vec.Vec Std.U8 × Array Std.U8 32#usize) tacenta_boundary.kem.KemError × R)

/-- `sign` fills one 64-byte buffer from the RNG and computes the signature from the secret, the
message and those bytes, touching the RNG nowhere else. -/
def SignFillsOnce64Of (sign : SignFn) : Prop :=
  ∃ S : Array Std.U8 32#usize → Slice Std.U8 → Slice Std.U8 → Array Std.U8 64#usize,
  ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (secret : Array Std.U8 32#usize) (message : Slice Std.U8) (rng : R),
    sign rc crc secret message rng =
      (do let (rng', z) ← rc.fill_bytes rng zeros64; ok (S secret message z, rng'))

/-- `generate` fills one 64-byte seed from the RNG and computes the key pair from it, touching the
RNG nowhere else. -/
def GenerateFillsOnce64Of (generate : GenerateFn) : Prop :=
  ∃ G : Slice Std.U8 → core.result.Result tacenta_kem.IncrementalKeyPair tacenta_kem.KemError,
  ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (rng : R),
    generate rc crc rng =
      (do let (rng', seed) ← rc.fill_bytes rng zeros64; ok (G seed, rng'))

/-- `encap` refuses a key that `valid` rejects before it reads the RNG, and otherwise fills one
32-byte buffer and computes its result from the key and those bytes. -/
def KemShapeOf (encap : EncapFn) : Prop :=
  ∃ (valid : Bytes → Bool) (E : Bytes → Bytes → alloc.vec.Vec Std.U8 × Array Std.U8 32#usize),
  ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (publicKey : Slice Std.U8) (rng : R),
    encap rc crc publicKey rng =
      if valid (sliceOf publicKey) then
        (do let (rng', m) ← rc.fill_bytes rng zeros32
            ok (core.result.Result.Ok (E (sliceOf publicKey) (sliceOf m)), rng'))
      else ok (.Err (), rng)

/-- The laws at the shipped constants. They are assumptions; no theorem here proves them. -/
def SignFillsOnce64 : Prop := SignFillsOnce64Of @tacenta_boundary.xeddsa.sign
def GenerateFillsOnce64 : Prop := GenerateFillsOnce64Of @tacenta_kem.IncrementalKeyPair.generate
def KemShape : Prop := KemShapeOf @tacenta_boundary.kem.encapsulate

/-! ### The clauses from the laws, at the byte-stream source -/

/-- The model's signing function a law's `S` determines: classically, the signature of the
secret, message and draws that the byte views name. -/
noncomputable def sigSignOf
    (S : Array Std.U8 32#usize → Slice Std.U8 → Slice Std.U8 → Array Std.U8 64#usize)
    (sk msg d1 d2 : Bytes) : Bytes := by
  classical
  exact if h : (∃ a : Array Std.U8 32#usize, arrayOf a = sk) ∧
      (∃ m : Slice Std.U8, sliceOf m = msg) ∧ (∃ z : Slice Std.U8, sliceOf z = d1 ++ d2) then
    arrayOf (S h.1.choose h.2.1.choose h.2.2.choose)
  else []

theorem sigSignClause_of_law
    (S : Array Std.U8 32#usize → Slice Std.U8 → Slice Std.U8 → Array Std.U8 64#usize)
    (sign : Array Std.U8 32#usize → Slice Std.U8 → List Std.U8 →
      Result (Array Std.U8 64#usize × List Std.U8))
    (hS : ∀ secret message rng, sign secret message rng =
      (do let (rng', z) ← byteRng.fill_bytes rng zeros64; ok (S secret message z, rng')))
    (oracle : Model.Lifecycle.Oracle) (hsig : oracle.sigSign = sigSignOf S) :
    SigSignClause sign byteTrace oracle := by
  intro secret message rng d1 d2 rest h
  obtain ⟨s, hf, htr, hsl⟩ := byte_fill_64 h
  refine ⟨S secret message s, rng.drop 64, ?_, htr, ?_⟩
  · rw [hS, hf]; rfl
  · rw [hsig]
    unfold sigSignOf
    have hex : (∃ a : Array Std.U8 32#usize, arrayOf a = arrayOf secret) ∧
        (∃ m : Slice Std.U8, sliceOf m = sliceOf message) ∧
        (∃ z : Slice Std.U8, sliceOf z = d1 ++ d2) := ⟨⟨secret, rfl⟩, ⟨message, rfl⟩, ⟨s, hsl⟩⟩
    rw [dif_pos hex]
    have e1 : hex.1.choose = secret :=
      Tacenta.DispatchEvidenceVacuity.arrayOf_inj hex.1.choose_spec
    have e2 : hex.2.1.choose = message :=
      Tacenta.DispatchEvidenceVacuity.sliceOf_inj hex.2.1.choose_spec
    have e3 : hex.2.2.choose = s :=
      Tacenta.DispatchEvidenceVacuity.sliceOf_inj (hex.2.2.choose_spec.trans hsl.symm)
    rw [e1, e2, e3]

/-- The model's KEM functions a law's `valid` and `E` determine. -/
def kemEncapsOf (valid : Bytes → Bool)
    (E : Bytes → Bytes → alloc.vec.Vec Std.U8 × Array Std.U8 32#usize)
    (publicKey draw : Bytes) : Option (Bytes × Model.Lifecycle.Key) :=
  if valid publicKey then some (vecOf (E publicKey draw).1, arrayOf (E publicKey draw).2)
  else none

theorem kemClauses_of_law (valid : Bytes → Bool)
    (E : Bytes → Bytes → alloc.vec.Vec Std.U8 × Array Std.U8 32#usize)
    (encap : Slice Std.U8 → List Std.U8 → Result (core.result.Result
      (alloc.vec.Vec Std.U8 × Array Std.U8 32#usize) tacenta_boundary.kem.KemError ×
        List Std.U8))
    (hK : ∀ publicKey rng, encap publicKey rng =
      if valid (sliceOf publicKey) then
        (do let (rng', m) ← byteRng.fill_bytes rng zeros32
            ok (core.result.Result.Ok (E (sliceOf publicKey) (sliceOf m)), rng'))
      else ok (.Err (), rng))
    (oracle : Model.Lifecycle.Oracle) (hv : oracle.kemValid = valid)
    (he : oracle.kemEncaps = kemEncapsOf valid E) :
    KemClauses encap byteTrace oracle := by
  refine ⟨?_, ?_, ?_⟩
  · intro publicKey rng d rest expected h hsome
    rw [he] at hsome
    unfold kemEncapsOf at hsome
    split at hsome
    · rename_i hvalid
      obtain ⟨s, hf, htr, hsl, _⟩ := byte_fill_32 h
      refine ⟨E (sliceOf publicKey) (sliceOf s), rng.drop 32, ?_, htr, ?_⟩
      · rw [hK, if_pos hvalid, hf]; rfl
      · rw [hsl]; exact hsome
    · simp at hsome
  · intro publicKey rng error hinv
    rw [hv] at hinv
    rw [hK, if_neg (by simp [hinv])]
  · intro publicKey rng error hcall
    rw [hK] at hcall
    by_cases hvalid : valid (sliceOf publicKey) = true
    · rw [if_pos hvalid] at hcall
      simp [byteRng] at hcall
    · refine ⟨by rw [hv]; simpa using hvalid, fun draw => ?_⟩
      rw [he]; unfold kemEncapsOf; simp [hvalid]

/-! ### The laws have a model with a refused key, and the clauses hold in it -/

def signModel : SignFn := fun rc _ _ _ rng => do
  let (rng', _) ← rc.fill_bytes rng zeros64
  ok (Array.repeat 64#usize 0#u8, rng')

def generateModel : GenerateFn := fun rc _ rng => do
  let (rng', _) ← rc.fill_bytes rng zeros64
  ok (.Err (), rng')

/-- A KEM that accepts exactly the keys of the ML-KEM-1024 public-key length, 1568 bytes. -/
def kemModelValid (publicKey : Bytes) : Bool := publicKey.length == 1568

def kemModelE (_ _ : Bytes) : alloc.vec.Vec Std.U8 × Array Std.U8 32#usize :=
  (alloc.vec.Vec.new Std.U8, Array.repeat 32#usize 0#u8)

def encapModel : EncapFn := fun rc _ publicKey rng =>
  if kemModelValid (sliceOf publicKey) then
    (do let (rng', m) ← rc.fill_bytes rng zeros32
        ok (core.result.Result.Ok (kemModelE (sliceOf publicKey) (sliceOf m)), rng'))
  else ok (.Err (), rng)

theorem signModel_law : SignFillsOnce64Of signModel :=
  ⟨fun _ _ _ => Array.repeat 64#usize 0#u8, fun _ _ _ _ _ => rfl⟩

theorem generateModel_law : GenerateFillsOnce64Of generateModel :=
  ⟨fun _ => .Err (), fun _ _ _ => rfl⟩

theorem encapModel_law : KemShapeOf encapModel :=
  ⟨kemModelValid, kemModelE, fun _ _ _ _ => rfl⟩

/-- The three clauses the integration changes (`sigSign`, the KEM clauses) and `random32`, at
one byte-stream source, for functions that meet the three laws, with a key the KEM refuses. -/
theorem changed_rng_clauses_have_a_model :
    ∃ oracle : Model.Lifecycle.Oracle,
      Random32Clause byteRng byteCrc byteTrace ∧
      SigSignClause (signModel byteRng byteCrc) byteTrace oracle ∧
      KemClauses (encapModel byteRng byteCrc) byteTrace oracle ∧
      oracle.kemValid [] = false ∧
      SignFillsOnce64Of signModel ∧ GenerateFillsOnce64Of generateModel ∧
      KemShapeOf encapModel := by
  refine ⟨{ Model.Lifecycle.Examples.toyOracle [] with
      kemValid := kemModelValid, kemEncaps := kemEncapsOf kemModelValid kemModelE,
      sigSign := sigSignOf (fun _ _ _ => Array.repeat 64#usize 0#u8) },
    byte_random32Clause, ?_, ?_, by decide, signModel_law, generateModel_law, encapModel_law⟩
  · exact sigSignClause_of_law (fun _ _ _ => Array.repeat 64#usize 0#u8)
      (signModel byteRng byteCrc) (fun _ _ _ => rfl) _ rfl
  · exact kemClauses_of_law kemModelValid kemModelE (encapModel byteRng byteCrc)
      (fun _ _ => rfl) _ rfl rfl

/-- The same at the shipped constants: under the signing and KEM laws, the changed clauses and
`random32` hold at the byte-stream source for one oracle. -/
theorem changed_rng_clauses_of_laws (hS : SignFillsOnce64) (hK : KemShape) :
    ∃ oracle : Model.Lifecycle.Oracle,
      Random32Clause byteRng byteCrc byteTrace ∧
      SigSignClause (tacenta_boundary.xeddsa.sign byteRng byteCrc) byteTrace oracle ∧
      KemClauses (tacenta_boundary.kem.encapsulate byteRng byteCrc) byteTrace oracle := by
  obtain ⟨S, hS⟩ := hS
  obtain ⟨valid, E, hK⟩ := hK
  refine ⟨{ Model.Lifecycle.Examples.toyOracle [] with
      kemValid := valid, kemEncaps := kemEncapsOf valid E, sigSign := sigSignOf S },
    byte_random32Clause, ?_, ?_⟩
  · exact sigSignClause_of_law S _ (fun secret message rng => hS byteRng byteCrc secret message rng)
      _ rfl
  · exact kemClauses_of_law valid E _ (fun publicKey rng => hK byteRng byteCrc publicKey rng)
      _ rfl rfl

/-! ## B'. The Braid's key generation draws a 64-byte seed -/

theorem bind_eq_ok_iff {α β : Type} {x : Result α} {f : α → Result β} {y : β} :
    (x >>= f) = ok y ↔ ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp

/-- A Braid send from `KeysUnsampled` returns the RNG state that key generation returned. -/
theorem braid_send_keysUnsampled_generate {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (b : tacenta_braid.Braid) (epoch : Std.U64)
    (auth : tacenta_braid.Auth) (hstate : b.state = .KeysUnsampled epoch auth)
    (rng rngNext : R)
    (out : tacenta_braid.Msg × Std.U64 × Option tacenta_braid.Output × tacenta_braid.Braid)
    (hcall : tacenta_braid.Braid.send rc crc b rng = ok (out, rngNext)) :
    ∃ r, tacenta_kem.IncrementalKeyPair.generate rc crc rng = ok (r, rngNext) := by
  unfold tacenta_braid.Braid.send at hcall
  rw [hstate] at hcall
  simp only [tacenta_braid.State.Insts.CoreCloneClone.clone, tacenta_braid.Braid.step_send,
    bind_tc_ok, lift] at hcall
  rcases hc : tacenta_braid.Auth.Insts.CoreCloneClone.clone auth with a | e | _
  · rw [hc] at hcall
    simp only [bind_tc_ok] at hcall
    rcases hg : tacenta_kem.IncrementalKeyPair.generate rc crc rng with ⟨r, rng1⟩ | e | _
    · refine ⟨r, ?_⟩
      rw [hg] at hcall
      simp only [bind_tc_ok] at hcall
      have key : rng1 = rngNext := by
        have hgen : ∀ (X : Result ((tacenta_braid.Msg × Option tacenta_braid.Output ×
            tacenta_braid.State) × R)),
            (∀ v, X = ok v → v.2 = rng1) →
            (do
              let ((msg, out, next), rng1) ← X
              let i ← tacenta_braid.Braid.reported { state := next }
              ok ((msg, i, out, ({ state := next } : tacenta_braid.Braid)), rng1)) = ok (out, rngNext) →
            rng1 = rngNext := by
          intro X hX h
          rcases hx : X with ⟨⟨msg, o, nxt⟩, rngA⟩ | _ | _ <;> rw [hx] at h
          · simp only [bind_tc_ok] at h
            have := hX _ hx
            dsimp only at h this
            rcases hr : tacenta_braid.Braid.reported { state := nxt } with i | _ | _
            · simp [hr] at h
              rw [← this]; exact h.2
            · simp [hr] at h
            · simp [hr] at h
          · simp at h
          · simp at h
        apply hgen _ _ hcall
        intro v hv
        cases r with
        | Ok kp =>
          simp [bind_eq_ok_iff] at hv
          obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hlast⟩ := hv
          rw [← hlast]
        | Err e =>
          simp [bind_eq_ok_iff] at hv
          obtain ⟨_, _, hlast⟩ := hv
          rw [← hlast]
      rw [key]
    · rw [hg] at hcall; simp at hcall
    · rw [hg] at hcall; simp at hcall
  · rw [hc] at hcall; simp at hcall
  · rw [hc] at hcall; simp at hcall

/-- `BraidSendTraceAgreement` lets a send from `KeysUnsampled` consume one trace entry, and
`OracleOf.sigSign` lets a signature consume two. Under the two laws both are one 64-byte fill from
the same state, so where two entries remain they cannot both hold. -/
theorem braidSendTrace_conflicts_with_sigSign
    (hsign : SignFillsOnce64) (hgen : GenerateFillsOnce64)
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {kem : KemView} {K : Model.Braid.Kem}
    {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session}
    {model : Model.Lifecycle.Session} {rng : R}
    (oracleOf : OracleOf rc crc dh kem trace oracle)
    (agreement : BraidSendTraceAgreement rc crc trace K oracle real model rng)
    (epoch : Std.U64) (auth : tacenta_braid.Auth)
    (hstate : real.braid.state = .KeysUnsampled epoch auth)
    (hdraw : Model.Lifecycle.braidSendNeedsDraw model.braid = true)
    (realMessage : tacenta_braid.Msg) (realEpoch : Std.U64)
    (realOutput : Option tacenta_braid.Output) (realBraidNext : tacenta_braid.Braid) (rngNext : R)
    (hcall : tacenta_braid.Braid.send rc crc real.braid rng =
      ok ((realMessage, realEpoch, realOutput, realBraidNext), rngNext))
    (draw1 draw2 : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key)
    (htrace : trace rng = draw1 :: draw2 :: rest) : False := by
  obtain ⟨draw, rest', hcons, hnext⟩ :=
    agreement.drawTrace realMessage realEpoch realOutput realBraidNext rngNext hcall hdraw
  rw [htrace] at hcons
  injection hcons with _ hrest
  obtain ⟨_, hgenCall⟩ := braid_send_keysUnsampled_generate rc crc real.braid epoch auth hstate
    rng rngNext _ hcall
  obtain ⟨G, hG⟩ := hgen
  rw [hG] at hgenCall
  obtain ⟨S, hS⟩ := hsign
  obtain ⟨_, rngSig, hsignCall, htraceSig⟩ :=
    oracleOf.sigSign (Array.repeat 32#usize 0#u8) zeros64 rng draw1 draw2 rest htrace
  rw [hS] at hsignCall
  rcases hf : rc.fill_bytes rng zeros64 with ⟨rngF, z⟩ | _ | _
  · rw [hf] at hgenCall hsignCall
    simp at hgenCall hsignCall
    have h1 : trace rngNext = draw2 :: rest := by rw [hnext, ← hrest]
    have h2 : trace rngNext = rest := by rw [← hgenCall.2, hsignCall.2]; exact htraceSig.1
    have := congrArg List.length (h1.symm.trans h2)
    simp at this
  · rw [hf] at hgenCall; simp at hgenCall
  · rw [hf] at hgenCall; simp at hgenCall

/-! ## C. The numeric state records hold at the model's initial Triple state -/

theorem retryReceiveBounds_initAlice (sk ourPub peerPub dhOut : Model.Lifecycle.Key)
    (labels : Model.State.LabelSet) (header : tacenta_triple.Header)
    (modelHeader : Model.State.Header) :
    RetryReceiveBounds (Model.Triple.initAlice sk ourPub peerPub dhOut labels) header
      modelHeader none := by
  have hu : 4294967295 ≤ Usize.max :=
    Tacenta.SessionUnitSessionT1.small_le_usize_max (le_refl _)
  constructor <;>
    simp [Model.Triple.initAlice, Model.Ratchet.initSender, Model.SparseRatchet.initAlice,
      Model.SparseRatchet.init, Model.State.maxSkippedStore, Model.State.maxSkip,
      Model.SparseRatchet.maxSkip, Model.SparseRatchet.epochsKept, U32.max_eq, U64.max_eq] <;>
    first | omega | (rintro ch (h | h) <;> subst h <;> simp)

/-- The record is not true of every state: a sparse epoch at `u64::MAX` fails it. -/
theorem retryReceiveBounds_not_trivial (state : Model.Triple.State)
    (header : tacenta_triple.Header) (modelHeader : Model.State.Header) :
    ¬ RetryReceiveBounds
      { state with postQuantum := { state.postQuantum with epoch := U64.max } }
      header modelHeader none := by
  intro h
  have := h.sparseEpoch
  simp at this

theorem generatedTripleRefusalConditions_initAlice [Tacenta.SessionUnitT1.DerivedKeysModel]
    (sk ourPub peerPub dhOut : Model.Lifecycle.Key) (labels : Model.State.LabelSet)
    (model : Model.Lifecycle.Session)
    (htriple : model.triple = Model.Triple.initAlice sk ourPub peerPub dhOut labels) :
    Nonempty (GeneratedTripleRefusalConditions model none) := by
  have hu : 4294967295 ≤ Usize.max :=
    Tacenta.SessionUnitSessionT1.small_le_usize_max (le_refl _)
  refine ⟨⟨inferInstance, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    simp [htriple, Model.Triple.initAlice, Model.SparseRatchet.initAlice,
      Model.SparseRatchet.init, Model.SparseRatchet.epochsKept, U64.max_eq] <;>
    first | omega | (rintro ch (h | h) <;> subst h <;> simp)

theorem generatedTripleSuccessConditions_initAlice [Tacenta.SessionUnitT1.DerivedKeysModel]
    (sk ourPub peerPub dhOut : Model.Lifecycle.Key) (labels : Model.State.LabelSet)
    (model : Model.Lifecycle.Session)
    (htriple : model.triple = Model.Triple.initAlice sk ourPub peerPub dhOut labels)
    (realEpoch : Std.U64) :
    Nonempty (GeneratedTripleSuccessConditions model realEpoch none) := by
  have hu : 4294967295 ≤ Usize.max :=
    Tacenta.SessionUnitSessionT1.small_le_usize_max (le_refl _)
  refine ⟨⟨inferInstance, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    simp [htriple, Model.Triple.initAlice, Model.SparseRatchet.initAlice,
      Model.SparseRatchet.init, Model.SparseRatchet.epochsKept, U64.max_eq] <;>
    first | omega | (rintro ch (h | h) <;> subst h <;> simp)

/-! ## D. The model's repeat recognition is not tied to the code by `OracleOf`

`Model.Lifecycle.sameEphemeralAgreement` hands the two 33-byte encoded ephemerals to
`oracle.dhAgree`, while `OracleOf.dhAgree` constrains `dhAgree` only at the 32-byte views the DH
codec produces. So whatever `OracleOf` holds, the oracle can be changed off those views, and the
model's verdict on a pair of strings that are not 32 bytes long can be made either value. The
premises `hmodelSame` and `hagreementMismatch` of the repeat constructors of
`SessionDecryptEvidence` and `InitialDispatchBranchEvidence` are therefore a choice of oracle, not
a fact the code supplies. -/

theorem oracleOf_dhAgree_off_view {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView}
    {kem : KemView} {oracle : Model.Lifecycle.Oracle}
    (codec : DhCodecOf dh) (oracleOf : OracleOf rc crc dh kem trace oracle)
    (f : Model.Lifecycle.Key → Model.Lifecycle.Key → Option Model.Lifecycle.Key)
    (hf : ∀ s p, p.length = 32 → f s p = oracle.dhAgree s p) :
    OracleOf rc crc dh kem trace { oracle with dhAgree := f } := by
  refine { oracleOf with dhAgree := ?_ }
  intro secret publicKey
  obtain ⟨result, hcall, hres⟩ := oracleOf.dhAgree secret publicKey
  refine ⟨result, hcall, ?_⟩
  obtain ⟨bytes, _, hbytes⟩ := codec.asBytes publicKey
  have hlen : (dh.publicKey publicKey).length = 32 := by
    rw [← hbytes, arrayOf, List.length_map]
    simp
  show result.map arrayOf = f (dh.privateKey secret) (dh.publicKey publicKey)
  rw [hf _ _ hlen]
  exact hres

theorem sameEphemeralAgreement_unconstrained {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView}
    {kem : KemView} {oracle : Model.Lifecycle.Oracle}
    (codec : DhCodecOf dh) (oracleOf : OracleOf rc crc dh kem trace oracle)
    (secret established incoming : Model.Lifecycle.Key)
    (hestablished : established.length ≠ 32) (hincoming : incoming.length ≠ 32) (b : Bool) :
    ∃ oracle' : Model.Lifecycle.Oracle,
      OracleOf rc crc dh kem trace oracle' ∧
      (∀ s p, p.length = 32 → oracle'.dhAgree s p = oracle.dhAgree s p) ∧
      Model.Lifecycle.sameEphemeralAgreement oracle' secret established incoming = b := by
  let f : Model.Lifecycle.Key → Model.Lifecycle.Key → Option Model.Lifecycle.Key :=
    fun s p => if p.length = 32 then oracle.dhAgree s p else if b then some [] else none
  have hf : ∀ s p, p.length = 32 → f s p = oracle.dhAgree s p := by
    intro s p hp
    simp [f, hp]
  refine ⟨{ oracle with dhAgree := f }, oracleOf_dhAgree_off_view codec oracleOf f hf,
    fun s p hp => hf s p hp, ?_⟩
  cases b <;> simp [Model.Lifecycle.sameEphemeralAgreement, f, hestablished, hincoming]

end Tacenta.UnitLifecycleIntegrationScreen

/-! ## Pins

The axiom list and the statement of each result, held by the build, and the text of each clause
and law definition (`#print`). `attest.py` requires every one of them (`REQUIRED_PINS`,
`REQUIRED_STATEMENT_PINS`). -/

/--
info: 'Tacenta.UnitLifecycleIntegrationScreen.concreteBranchEvidence_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.sign,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleIntegrationScreen.concreteBranchEvidence_empty

/--
info: @Tacenta.UnitLifecycleIntegrationScreen.concreteBranchEvidence_empty : ∀ {R : Type} {rc : rand_core_1.RngCore R}
  {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView} {kem : KemView}
  {K : Model.Braid.Kem} {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
  {real : lifecycle.Session} {model : Model.Lifecycle.Session},
  OracleOf rc crc dh kem trace oracle →
    ∀ (message : Slice U8) (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes)
      (dhOutRecv : Model.Lifecycle.Key),
      Model.CompositeHeader.decodeDetailed (sliceOf message) = Except.ok (composite, ciphertext) →
        oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv →
          ∀ (rng : R), InitialRatchetConcreteBranchEvidence → False
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleIntegrationScreen.concreteBranchEvidence_empty

/--
info: 'Tacenta.UnitLifecycleIntegrationScreen.endToEndEvidence_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.sign,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleIntegrationScreen.endToEndEvidence_empty

/--
info: @Tacenta.UnitLifecycleIntegrationScreen.endToEndEvidence_empty : ∀ {R : Type} {rc : rand_core_1.RngCore R}
  {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView} {kem : KemView}
  {K : Model.Braid.Kem} {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
  {real : lifecycle.Session} {model : Model.Lifecycle.Session},
  OracleOf rc crc dh kem trace oracle →
    ∀ (message : Slice U8) (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes)
      (dhOutRecv : Model.Lifecycle.Key),
      Model.CompositeHeader.decodeDetailed (sliceOf message) = Except.ok (composite, ciphertext) →
        oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv →
          ∀ (outerMessage : Slice U8) (rng : R), InitialRatchetEndToEndEvidence outerMessage rng → False
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleIntegrationScreen.endToEndEvidence_empty

/--
info: 'Tacenta.UnitLifecycleIntegrationScreen.agreementEndToEndEvidence_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.sign,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleIntegrationScreen.agreementEndToEndEvidence_empty

/--
info: @Tacenta.UnitLifecycleIntegrationScreen.agreementEndToEndEvidence_empty : ∀ {R : Type} {rc : rand_core_1.RngCore R}
  {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView} {kem : KemView}
  {K : Model.Braid.Kem} {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
  {real : lifecycle.Session} {model : Model.Lifecycle.Session},
  OracleOf rc crc dh kem trace oracle →
    ∀ (message : Slice U8) (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes)
      (dhOutRecv : Model.Lifecycle.Key),
      Model.CompositeHeader.decodeDetailed (sliceOf message) = Except.ok (composite, ciphertext) →
        oracle.dhAgree model.ratchetPrivate composite.dh = some dhOutRecv →
          ∀ (outerMessage : Slice U8) (rng : R), InitialAgreementRatchetEndToEndEvidence outerMessage rng → False
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleIntegrationScreen.agreementEndToEndEvidence_empty

/--
info: 'Tacenta.UnitLifecycleIntegrationScreen.byte_random32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleIntegrationScreen.byte_random32

/--
info: Tacenta.UnitLifecycleIntegrationScreen.byte_random32 : ∀ (crc : rand_core_1.CryptoRng (List U8)) (rng : List U8)
  (draw : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
  Tacenta.UnitLifecycleIntegrationScreen.byteTrace rng = draw :: rest →
    ∃ value rng',
      lifecycle.random_secret Tacenta.UnitLifecycleIntegrationScreen.byteRng crc rng = ok (value, rng') ∧
        arrayOf value = draw ∧ Tacenta.UnitLifecycleIntegrationScreen.byteTrace rng' = rest
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleIntegrationScreen.byte_random32

/--
info: 'Tacenta.UnitLifecycleIntegrationScreen.random32Clause_of_oracleOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.sign,
 tacenta_boundary.xeddsa.verify,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleIntegrationScreen.random32Clause_of_oracleOf

/--
info: @Tacenta.UnitLifecycleIntegrationScreen.random32Clause_of_oracleOf : ∀ {R : Type} {rc : rand_core_1.RngCore R}
  {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView} {kem : KemView}
  {oracle : Model.Lifecycle.Oracle},
  OracleOf rc crc dh kem trace oracle → Tacenta.UnitLifecycleIntegrationScreen.Random32Clause rc crc trace
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleIntegrationScreen.random32Clause_of_oracleOf

/--
info: 'Tacenta.UnitLifecycleIntegrationScreen.sigSignClause_of_oracleOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.sign,
 tacenta_boundary.xeddsa.verify,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleIntegrationScreen.sigSignClause_of_oracleOf

/--
info: @Tacenta.UnitLifecycleIntegrationScreen.sigSignClause_of_oracleOf : ∀ {R : Type} {rc : rand_core_1.RngCore R}
  {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView} {kem : KemView}
  {oracle : Model.Lifecycle.Oracle},
  OracleOf rc crc dh kem trace oracle →
    Tacenta.UnitLifecycleIntegrationScreen.SigSignClause (tacenta_boundary.xeddsa.sign rc crc) trace oracle
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleIntegrationScreen.sigSignClause_of_oracleOf

/--
info: 'Tacenta.UnitLifecycleIntegrationScreen.kemClauses_of_oracleOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.sign,
 tacenta_boundary.xeddsa.verify,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleIntegrationScreen.kemClauses_of_oracleOf

/--
info: @Tacenta.UnitLifecycleIntegrationScreen.kemClauses_of_oracleOf : ∀ {R : Type} {rc : rand_core_1.RngCore R}
  {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView} {kem : KemView}
  {oracle : Model.Lifecycle.Oracle},
  OracleOf rc crc dh kem trace oracle →
    Tacenta.UnitLifecycleIntegrationScreen.KemClauses (tacenta_boundary.kem.encapsulate rc crc) trace oracle
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleIntegrationScreen.kemClauses_of_oracleOf

/--
info: 'Tacenta.UnitLifecycleIntegrationScreen.sigSignClause_of_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleIntegrationScreen.sigSignClause_of_law

/--
info: Tacenta.UnitLifecycleIntegrationScreen.sigSignClause_of_law : ∀
  (S : Std.Array U8 32#usize → Slice U8 → Slice U8 → Std.Array U8 64#usize)
  (sign : Std.Array U8 32#usize → Slice U8 → List U8 → Result (Std.Array U8 64#usize × List U8)),
  (∀ (secret : Std.Array U8 32#usize) (message : Slice U8) (rng : List U8),
      sign secret message rng = do
        let (rng', z) ←
          Tacenta.UnitLifecycleIntegrationScreen.byteRng.fill_bytes rng Tacenta.UnitLifecycleIntegrationScreen.zeros64
        ok (S secret message z, rng')) →
    ∀ (oracle : Model.Lifecycle.Oracle),
      oracle.sigSign = Tacenta.UnitLifecycleIntegrationScreen.sigSignOf S →
        Tacenta.UnitLifecycleIntegrationScreen.SigSignClause sign Tacenta.UnitLifecycleIntegrationScreen.byteTrace
          oracle
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleIntegrationScreen.sigSignClause_of_law

/--
info: 'Tacenta.UnitLifecycleIntegrationScreen.kemClauses_of_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleIntegrationScreen.kemClauses_of_law

/--
info: Tacenta.UnitLifecycleIntegrationScreen.kemClauses_of_law : ∀ (valid : Bytes → Bool)
  (E : Bytes → Bytes → alloc.vec.Vec U8 × Std.Array U8 32#usize)
  (encap :
    Slice U8 →
      List U8 →
        Result (core.result.Result (alloc.vec.Vec U8 × Std.Array U8 32#usize) tacenta_boundary.kem.KemError × List U8)),
  (∀ (publicKey : Slice U8) (rng : List U8),
      encap publicKey rng =
        if valid (sliceOf publicKey) = true then do
          let (rng', m) ←
            Tacenta.UnitLifecycleIntegrationScreen.byteRng.fill_bytes rng Tacenta.UnitLifecycleIntegrationScreen.zeros32
          ok (core.result.Result.Ok (E (sliceOf publicKey) (sliceOf m)), rng')
        else ok (core.result.Result.Err (), rng)) →
    ∀ (oracle : Model.Lifecycle.Oracle),
      oracle.kemValid = valid →
        oracle.kemEncaps = Tacenta.UnitLifecycleIntegrationScreen.kemEncapsOf valid E →
          Tacenta.UnitLifecycleIntegrationScreen.KemClauses encap Tacenta.UnitLifecycleIntegrationScreen.byteTrace
            oracle
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleIntegrationScreen.kemClauses_of_law

/--
info: 'Tacenta.UnitLifecycleIntegrationScreen.changed_rng_clauses_have_a_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.IncrementalKeyPair,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleIntegrationScreen.changed_rng_clauses_have_a_model

/--
info: Tacenta.UnitLifecycleIntegrationScreen.changed_rng_clauses_have_a_model : ∃ oracle,
  Tacenta.UnitLifecycleIntegrationScreen.Random32Clause Tacenta.UnitLifecycleIntegrationScreen.byteRng
      Tacenta.UnitLifecycleIntegrationScreen.byteCrc Tacenta.UnitLifecycleIntegrationScreen.byteTrace ∧
    Tacenta.UnitLifecycleIntegrationScreen.SigSignClause
        (Tacenta.UnitLifecycleIntegrationScreen.signModel Tacenta.UnitLifecycleIntegrationScreen.byteRng
          Tacenta.UnitLifecycleIntegrationScreen.byteCrc)
        Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracle ∧
      Tacenta.UnitLifecycleIntegrationScreen.KemClauses
          (Tacenta.UnitLifecycleIntegrationScreen.encapModel Tacenta.UnitLifecycleIntegrationScreen.byteRng
            Tacenta.UnitLifecycleIntegrationScreen.byteCrc)
          Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracle ∧
        oracle.kemValid [] = false ∧
          (Tacenta.UnitLifecycleIntegrationScreen.SignFillsOnce64Of fun {R} =>
              Tacenta.UnitLifecycleIntegrationScreen.signModel) ∧
            (Tacenta.UnitLifecycleIntegrationScreen.GenerateFillsOnce64Of fun {R} =>
                Tacenta.UnitLifecycleIntegrationScreen.generateModel) ∧
              Tacenta.UnitLifecycleIntegrationScreen.KemShapeOf fun {R} =>
                Tacenta.UnitLifecycleIntegrationScreen.encapModel
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleIntegrationScreen.changed_rng_clauses_have_a_model

/--
info: 'Tacenta.UnitLifecycleIntegrationScreen.changed_rng_clauses_of_laws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.sign]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleIntegrationScreen.changed_rng_clauses_of_laws

/--
info: Tacenta.UnitLifecycleIntegrationScreen.changed_rng_clauses_of_laws : Tacenta.UnitLifecycleIntegrationScreen.SignFillsOnce64 →
  Tacenta.UnitLifecycleIntegrationScreen.KemShape →
    ∃ oracle,
      Tacenta.UnitLifecycleIntegrationScreen.Random32Clause Tacenta.UnitLifecycleIntegrationScreen.byteRng
          Tacenta.UnitLifecycleIntegrationScreen.byteCrc Tacenta.UnitLifecycleIntegrationScreen.byteTrace ∧
        Tacenta.UnitLifecycleIntegrationScreen.SigSignClause
            (tacenta_boundary.xeddsa.sign Tacenta.UnitLifecycleIntegrationScreen.byteRng
              Tacenta.UnitLifecycleIntegrationScreen.byteCrc)
            Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracle ∧
          Tacenta.UnitLifecycleIntegrationScreen.KemClauses
            (tacenta_boundary.kem.encapsulate Tacenta.UnitLifecycleIntegrationScreen.byteRng
              Tacenta.UnitLifecycleIntegrationScreen.byteCrc)
            Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracle
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleIntegrationScreen.changed_rng_clauses_of_laws

/--
info: 'Tacenta.UnitLifecycleIntegrationScreen.braid_send_keysUnsampled_generate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 core.num.Usize.div_ceil,
 zeroize.Zeroize.Blanket.zeroize,
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
#print axioms Tacenta.UnitLifecycleIntegrationScreen.braid_send_keysUnsampled_generate

/--
info: @Tacenta.UnitLifecycleIntegrationScreen.braid_send_keysUnsampled_generate : ∀ {R : Type} (rc : rand_core_1.RngCore R)
  (crc : rand_core_1.CryptoRng R) (b : tacenta_braid.Braid) (epoch : U64) (auth : tacenta_braid.Auth),
  b.state = tacenta_braid.State.KeysUnsampled epoch auth →
    ∀ (rng rngNext : R) (out : tacenta_braid.Msg × U64 × Option tacenta_braid.Output × tacenta_braid.Braid),
      tacenta_braid.Braid.send rc crc b rng = ok (out, rngNext) →
        ∃ r, tacenta_kem.IncrementalKeyPair.generate rc crc rng = ok (r, rngNext)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleIntegrationScreen.braid_send_keysUnsampled_generate

/--
info: 'Tacenta.UnitLifecycleIntegrationScreen.braidSendTrace_conflicts_with_sigSign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.sign,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 zeroize.Zeroize.Blanket.zeroize,
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
#print axioms Tacenta.UnitLifecycleIntegrationScreen.braidSendTrace_conflicts_with_sigSign

/--
info: Tacenta.UnitLifecycleIntegrationScreen.braidSendTrace_conflicts_with_sigSign : Tacenta.UnitLifecycleIntegrationScreen.SignFillsOnce64 →
  Tacenta.UnitLifecycleIntegrationScreen.GenerateFillsOnce64 →
    ∀ {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key}
      {dh : DhView} {kem : KemView} {K : Model.Braid.Kem} {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session}
      {model : Model.Lifecycle.Session} {rng : R},
      OracleOf rc crc dh kem trace oracle →
        BraidSendTraceAgreement rc crc trace K oracle real model rng →
          ∀ (epoch : U64) (auth : tacenta_braid.Auth),
            real.braid.state = tacenta_braid.State.KeysUnsampled epoch auth →
              Model.Lifecycle.braidSendNeedsDraw model.braid = true →
                ∀ (realMessage : tacenta_braid.Msg) (realEpoch : U64) (realOutput : Option tacenta_braid.Output)
                  (realBraidNext : tacenta_braid.Braid) (rngNext : R),
                  tacenta_braid.Braid.send rc crc real.braid rng =
                      ok ((realMessage, realEpoch, realOutput, realBraidNext), rngNext) →
                    ∀ (draw1 draw2 : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
                      trace rng = draw1 :: draw2 :: rest → False
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleIntegrationScreen.braidSendTrace_conflicts_with_sigSign

/--
info: 'Tacenta.UnitLifecycleIntegrationScreen.retryReceiveBounds_initAlice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleIntegrationScreen.retryReceiveBounds_initAlice

/--
info: Tacenta.UnitLifecycleIntegrationScreen.retryReceiveBounds_initAlice : ∀ (sk ourPub peerPub dhOut : Model.Lifecycle.Key)
  (labels : Model.State.LabelSet) (header : tacenta_triple.Header) (modelHeader : Model.State.Header),
  RetryReceiveBounds (Model.Triple.initAlice sk ourPub peerPub dhOut labels) header modelHeader none
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleIntegrationScreen.retryReceiveBounds_initAlice

/--
info: 'Tacenta.UnitLifecycleIntegrationScreen.retryReceiveBounds_not_trivial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleIntegrationScreen.retryReceiveBounds_not_trivial

/--
info: Tacenta.UnitLifecycleIntegrationScreen.retryReceiveBounds_not_trivial : ∀ (state : Model.Triple.State)
  (header : tacenta_triple.Header) (modelHeader : Model.State.Header),
  ¬RetryReceiveBounds
      { classical := state.classical,
        postQuantum :=
          have __src := state.postQuantum;
          { rk := __src.rk, epoch := U64.max, chains := __src.chains, skipped := __src.skipped,
            direction := __src.direction } }
      header modelHeader none
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleIntegrationScreen.retryReceiveBounds_not_trivial

/--
info: 'Tacenta.UnitLifecycleIntegrationScreen.generatedTripleRefusalConditions_initAlice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 zeroize.Zeroizing,
 zeroize.Zeroizing.new,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleIntegrationScreen.generatedTripleRefusalConditions_initAlice

/--
info: @Tacenta.UnitLifecycleIntegrationScreen.generatedTripleRefusalConditions_initAlice : ∀
  [Tacenta.SessionUnitT1.DerivedKeysModel] (sk ourPub peerPub dhOut : Model.Lifecycle.Key)
  (labels : Model.State.LabelSet) (model : Model.Lifecycle.Session),
  model.triple = Model.Triple.initAlice sk ourPub peerPub dhOut labels →
    Nonempty (GeneratedTripleRefusalConditions model none)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleIntegrationScreen.generatedTripleRefusalConditions_initAlice

/--
info: 'Tacenta.UnitLifecycleIntegrationScreen.generatedTripleSuccessConditions_initAlice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 zeroize.Zeroizing,
 zeroize.Zeroizing.new,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleIntegrationScreen.generatedTripleSuccessConditions_initAlice

/--
info: @Tacenta.UnitLifecycleIntegrationScreen.generatedTripleSuccessConditions_initAlice : ∀
  [Tacenta.SessionUnitT1.DerivedKeysModel] (sk ourPub peerPub dhOut : Model.Lifecycle.Key)
  (labels : Model.State.LabelSet) (model : Model.Lifecycle.Session),
  model.triple = Model.Triple.initAlice sk ourPub peerPub dhOut labels →
    ∀ (realEpoch : U64), Nonempty (GeneratedTripleSuccessConditions model realEpoch none)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleIntegrationScreen.generatedTripleSuccessConditions_initAlice

/--
info: 'Tacenta.UnitLifecycleIntegrationScreen.oracleOf_dhAgree_off_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.sign,
 tacenta_boundary.xeddsa.verify,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleIntegrationScreen.oracleOf_dhAgree_off_view

/--
info: @Tacenta.UnitLifecycleIntegrationScreen.oracleOf_dhAgree_off_view : ∀ {R : Type} {rc : rand_core_1.RngCore R}
  {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView} {kem : KemView}
  {oracle : Model.Lifecycle.Oracle},
  DhCodecOf dh →
    OracleOf rc crc dh kem trace oracle →
      ∀ (f : Model.Lifecycle.Key → Model.Lifecycle.Key → Option Model.Lifecycle.Key),
        (∀ (s p : Model.Lifecycle.Key), List.length p = 32 → f s p = oracle.dhAgree s p) →
          OracleOf rc crc dh kem trace
            { draws := oracle.draws, braidKem := oracle.braidKem, dhPublic := oracle.dhPublic, dhAgree := f,
              identityValid := oracle.identityValid, aeadSeal := oracle.aeadSeal, aeadOpen := oracle.aeadOpen,
              kemValid := oracle.kemValid, kemEncaps := oracle.kemEncaps, kemDecaps := oracle.kemDecaps,
              sigVerify := oracle.sigVerify, sigSign := oracle.sigSign }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleIntegrationScreen.oracleOf_dhAgree_off_view

/--
info: 'Tacenta.UnitLifecycleIntegrationScreen.sameEphemeralAgreement_unconstrained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.sign,
 tacenta_boundary.xeddsa.verify,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleIntegrationScreen.sameEphemeralAgreement_unconstrained

/--
info: @Tacenta.UnitLifecycleIntegrationScreen.sameEphemeralAgreement_unconstrained : ∀ {R : Type} {rc : rand_core_1.RngCore R}
  {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView} {kem : KemView}
  {oracle : Model.Lifecycle.Oracle},
  DhCodecOf dh →
    OracleOf rc crc dh kem trace oracle →
      ∀ (secret established incoming : Model.Lifecycle.Key),
        List.length established ≠ 32 →
          List.length incoming ≠ 32 →
            ∀ (b : Bool),
              ∃ oracle',
                OracleOf rc crc dh kem trace oracle' ∧
                  (∀ (s p : Model.Lifecycle.Key), List.length p = 32 → oracle'.dhAgree s p = oracle.dhAgree s p) ∧
                    Model.Lifecycle.sameEphemeralAgreement oracle' secret established incoming = b
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleIntegrationScreen.sameEphemeralAgreement_unconstrained

/--
info: def Tacenta.UnitLifecycleIntegrationScreen.Random32Clause : {R : Type} →
  rand_core_1.RngCore R → rand_core_1.CryptoRng R → (R → List Model.Lifecycle.Key) → Prop :=
fun {R} rc crc trace =>
  ∀ (rng : R) (draw : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
    trace rng = draw :: rest →
      ∃ value rng', lifecycle.random_secret rc crc rng = ok (value, rng') ∧ arrayOf value = draw ∧ trace rng' = rest
-/
#guard_msgs in
#print Tacenta.UnitLifecycleIntegrationScreen.Random32Clause

/--
info: def Tacenta.UnitLifecycleIntegrationScreen.SigSignClause : {R : Type} →
  (Std.Array U8 32#usize → Slice U8 → R → Result (Std.Array U8 64#usize × R)) →
    (R → List Model.Lifecycle.Key) → Model.Lifecycle.Oracle → Prop :=
fun {R} sign trace oracle =>
  ∀ (secret : Std.Array U8 32#usize) (message : Slice U8) (rng : R) (draw1 draw2 : Model.Lifecycle.Key)
    (rest : List Model.Lifecycle.Key),
    trace rng = draw1 :: draw2 :: rest →
      ∃ signature rng',
        sign secret message rng = ok (signature, rng') ∧
          trace rng' = rest ∧ arrayOf signature = oracle.sigSign (arrayOf secret) (sliceOf message) draw1 draw2
-/
#guard_msgs in
#print Tacenta.UnitLifecycleIntegrationScreen.SigSignClause

/--
info: def Tacenta.UnitLifecycleIntegrationScreen.KemClauses : {R : Type} →
  (Slice U8 →
      R → Result (core.result.Result (alloc.vec.Vec U8 × Std.Array U8 32#usize) tacenta_boundary.kem.KemError × R)) →
    (R → List Model.Lifecycle.Key) → Model.Lifecycle.Oracle → Prop :=
fun {R} encap trace oracle =>
  (∀ (publicKey : Slice U8) (rng : R) (draw : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key)
      (expected : Model.Lifecycle.Bytes × Model.Lifecycle.Key),
      trace rng = draw :: rest →
        oracle.kemEncaps (sliceOf publicKey) draw = some expected →
          ∃ result rng',
            encap publicKey rng = ok (core.result.Result.Ok result, rng') ∧
              trace rng' = rest ∧ encapsulationOf (core.result.Result.Ok result) = some expected) ∧
    (∀ (publicKey : Slice U8) (rng : R) (error : tacenta_boundary.kem.KemError),
        oracle.kemValid (sliceOf publicKey) = false → encap publicKey rng = ok (core.result.Result.Err error, rng)) ∧
      ∀ (publicKey : Slice U8) (rng : R) (error : tacenta_boundary.kem.KemError),
        encap publicKey rng = ok (core.result.Result.Err error, rng) →
          oracle.kemValid (sliceOf publicKey) = false ∧
            ∀ (draw : Model.Lifecycle.Key), oracle.kemEncaps (sliceOf publicKey) draw = none
-/
#guard_msgs in
#print Tacenta.UnitLifecycleIntegrationScreen.KemClauses

/--
info: def Tacenta.UnitLifecycleIntegrationScreen.SignFillsOnce64Of : Tacenta.UnitLifecycleIntegrationScreen.SignFn → Prop :=
fun sign =>
  ∃ S,
    ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (secret : Std.Array U8 32#usize)
      (message : Slice U8) (rng : R),
      sign rc crc secret message rng = do
        let (rng', z) ← rc.fill_bytes rng Tacenta.UnitLifecycleIntegrationScreen.zeros64
        ok (S secret message z, rng')
-/
#guard_msgs in
#print Tacenta.UnitLifecycleIntegrationScreen.SignFillsOnce64Of

/--
info: def Tacenta.UnitLifecycleIntegrationScreen.GenerateFillsOnce64Of : Tacenta.UnitLifecycleIntegrationScreen.GenerateFn →
  Prop :=
fun generate =>
  ∃ G,
    ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (rng : R),
      generate rc crc rng = do
        let (rng', seed) ← rc.fill_bytes rng Tacenta.UnitLifecycleIntegrationScreen.zeros64
        ok (G seed, rng')
-/
#guard_msgs in
#print Tacenta.UnitLifecycleIntegrationScreen.GenerateFillsOnce64Of

/--
info: def Tacenta.UnitLifecycleIntegrationScreen.KemShapeOf : Tacenta.UnitLifecycleIntegrationScreen.EncapFn → Prop :=
fun encap =>
  ∃ valid E,
    ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (publicKey : Slice U8) (rng : R),
      encap rc crc publicKey rng =
        if valid (sliceOf publicKey) = true then do
          let (rng', m) ← rc.fill_bytes rng Tacenta.UnitLifecycleIntegrationScreen.zeros32
          ok (core.result.Result.Ok (E (sliceOf publicKey) (sliceOf m)), rng')
        else ok (core.result.Result.Err (), rng)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleIntegrationScreen.KemShapeOf

/--
info: def Tacenta.UnitLifecycleIntegrationScreen.SignFillsOnce64 : Prop :=
Tacenta.UnitLifecycleIntegrationScreen.SignFillsOnce64Of @tacenta_boundary.xeddsa.sign
-/
#guard_msgs in
#print Tacenta.UnitLifecycleIntegrationScreen.SignFillsOnce64

/--
info: def Tacenta.UnitLifecycleIntegrationScreen.GenerateFillsOnce64 : Prop :=
Tacenta.UnitLifecycleIntegrationScreen.GenerateFillsOnce64Of @tacenta_kem.IncrementalKeyPair.generate
-/
#guard_msgs in
#print Tacenta.UnitLifecycleIntegrationScreen.GenerateFillsOnce64

/--
info: def Tacenta.UnitLifecycleIntegrationScreen.KemShape : Prop :=
Tacenta.UnitLifecycleIntegrationScreen.KemShapeOf @tacenta_boundary.kem.encapsulate
-/
#guard_msgs in
#print Tacenta.UnitLifecycleIntegrationScreen.KemShape
