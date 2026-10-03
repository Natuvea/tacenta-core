import Translation.UnitOracleDh

/-!
# The KEM decapsulation and signature verification clauses, and a guarded KEM success clause

`UnitLifecycleIntegrationScreen.lean` left `kemDecapsulate` and `sigVerify` undecided, and showed
that `OracleOf`'s KEM success clause binds the code only where the model's `kemEncaps` returns
`some`, so an oracle that never encapsulates meets it.

## Decisions

* `kemDecapsulate` and `sigVerify`: satisfiable, jointly with #220's axiom base and #234's laws, by
  an oracle that is not degenerate. `UnitOracleShape.lean` derives each from its law
  (`kemDecapsulateClause_of_laws`: `decapsulate` returns and the key-pair view is injective;
  `sigVerifyClause_of_laws`: `verify` returns and the public-key view is injective).
  `kem_sig_clauses_in_model`, here, shows both at the joint interpretation: the oracle decapsulates
  what it encapsulates and refuses the empty ciphertext, and verification accepts the oracle's own
  signature under the oracle's public key and refuses another.
* The KEM success clause: a new clause, `KemGuardedClause`, guarded by `kemValid` and not by the
  model's prediction: whenever the oracle accepts the key and the trace has a draw, the code
  encapsulates, consumes that draw, and returns what `kemEncaps` names. `OracleOfGuarded` is
  `OracleOf` with this clause added; `OracleOf` itself is unchanged.
  - `kemGuardedClause_of_law`: it follows from #234's `KemShapeOf` at the byte-stream source, for
    the oracle whose `kemValid` and `kemEncaps` the law determines.
  - `kemClauses_of_guarded`: with the two refusal clauses of `OracleOf`, it gives `OracleOf`'s
    conditional success clause, so the new record is a strengthening of the old.
  - `never_encapsulating_meets_kemClauses`, `never_encapsulating_fails_guarded`,
    `guarded_separates_never_encapsulating`: an oracle whose `kemEncaps` never returns `some` meets
    the three KEM clauses of `OracleOf` at any encapsulation that meets the law, when its validity
    verdict is the law's, and fails the
    guarded clause as soon as it accepts one key at a state with a draw; at the model's
    encapsulation there is such an oracle.
  - `kem_sig_clauses_in_model`: the joint model's oracle meets the guarded clause, accepts a
    1568-byte key and refuses the empty one, and its `kemEncaps` returns `some` at the accepted key
    for every draw, so the code encapsulates there.

What this does not show: that the real `decapsulate`, `verify` or `encapsulate` compute ML-KEM or
XEdDSA. The model's KEM and signature are toys.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3
open Tacenta.UnitOracleShape
open Tacenta.UnitOracleModel

namespace Tacenta.UnitOracleKemSig

open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace zeros32 kemModelValid
  kemEncapsOf KemClauses byte_fill_32 chunks32 zeroSlice sigSignOf)

/-! ## The guarded KEM success clause -/

/-- The KEM success clause guarded by the oracle's validity verdict, stated of a function
argument like the screen's `KemClauses`. -/
def KemGuardedClause {R : Type}
    (encap : Slice U8 → R → Result (core.result.Result
      (alloc.vec.Vec U8 × Array U8 32#usize) tacenta_boundary.kem.KemError × R))
    (trace : R → List Model.Lifecycle.Key) (oracle : Model.Lifecycle.Oracle) : Prop :=
  ∀ publicKey rng draw rest,
    oracle.kemValid (sliceOf publicKey) = true →
    trace rng = draw :: rest →
    ∃ result rng', encap publicKey rng = ok (.Ok result, rng') ∧
      trace rng' = rest ∧
      encapsulationOf (.Ok result) = oracle.kemEncaps (sliceOf publicKey) draw

/-- **`OracleOf` with the guarded KEM success clause.** A new record; `OracleOf` is unchanged. -/
structure OracleOfGuarded {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (dh : DhView) (kem : KemView) (trace : R → List Model.Lifecycle.Key)
    (oracle : Model.Lifecycle.Oracle) : Prop
    extends OracleOf rngCore cryptoRng dh kem trace oracle where
  kemEncapsulateGuarded : ∀ publicKey rng draw rest,
    oracle.kemValid (sliceOf publicKey) = true →
    trace rng = draw :: rest →
    ∃ result rng',
      tacenta_boundary.kem.encapsulate rngCore cryptoRng publicKey rng = ok (.Ok result, rng') ∧
      trace rng' = rest ∧
      encapsulationOf (.Ok result) = oracle.kemEncaps (sliceOf publicKey) draw

/-- The new record is the shape and the guarded clause at the real constants. -/
theorem oracleOfGuarded_iff_shape {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (dh : DhView) (kem : KemView) (trace : R → List Model.Lifecycle.Key)
    (oracle : Model.Lifecycle.Oracle) :
    OracleOfGuarded rc crc dh kem trace oracle ↔
      OracleOfShape InterpO.real rc crc (dhViewOf dh) (kemViewOf kem) trace oracle ∧
      KemGuardedClause (InterpO.real.kemEncapsulate rc crc) trace oracle :=
  ⟨fun h => ⟨(oracleOf_iff_shape rc crc dh kem trace oracle).mp h.toOracleOf,
      h.kemEncapsulateGuarded⟩,
   fun h => { toOracleOf := (oracleOf_iff_shape rc crc dh kem trace oracle).mpr h.1
              kemEncapsulateGuarded := h.2 }⟩

/-- The guarded clause from #234's KEM law, at the byte-stream source. -/
theorem kemGuardedClause_of_law (valid : Bytes → Bool)
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
    KemGuardedClause encap byteTrace oracle := by
  intro publicKey rng draw rest hvalid htrace
  rw [hv] at hvalid
  obtain ⟨s, hf, htr, hsl, _⟩ := byte_fill_32 htrace
  refine ⟨E (sliceOf publicKey) (sliceOf s), rng.drop 32, ?_, htr, ?_⟩
  · rw [hK, if_pos hvalid, hf]; rfl
  · rw [he, ← hsl]
    simp [kemEncapsOf, hvalid, encapsulationOf, resultOptionOf]

/-- **The guarded clause is a strengthening:** with the two refusal clauses of `OracleOf` it gives
`OracleOf`'s conditional success clause, so `KemClauses` holds. -/
theorem kemClauses_of_guarded {R : Type}
    (encap : Slice U8 → R → Result (core.result.Result
      (alloc.vec.Vec U8 × Array U8 32#usize) tacenta_boundary.kem.KemError × R))
    (trace : R → List Model.Lifecycle.Key) (oracle : Model.Lifecycle.Oracle)
    (hguarded : KemGuardedClause encap trace oracle)
    (hinvalid : ∀ publicKey rng error, oracle.kemValid (sliceOf publicKey) = false →
      encap publicKey rng = ok (.Err error, rng))
    (herror : ∀ publicKey rng error, encap publicKey rng = ok (.Err error, rng) →
      oracle.kemValid (sliceOf publicKey) = false ∧
      ∀ draw, oracle.kemEncaps (sliceOf publicKey) draw = none) :
    KemClauses encap trace oracle := by
  refine ⟨?_, hinvalid, herror⟩
  intro publicKey rng draw rest expected htrace hsome
  cases hval : oracle.kemValid (sliceOf publicKey) with
  | false =>
    have := (herror publicKey rng () (hinvalid publicKey rng () hval)).2 draw
    rw [this] at hsome
    cases hsome
  | true =>
    obtain ⟨result, rng', hcall, htr, henc⟩ := hguarded publicKey rng draw rest hval htrace
    exact ⟨result, rng', hcall, htr, henc.trans hsome⟩

/-- An oracle whose `kemEncaps` never returns `some` meets the three KEM clauses of `OracleOf` at
any encapsulation that meets #234's law, at the byte-stream source. -/
theorem never_encapsulating_meets_kemClauses (valid : Bytes → Bool)
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
    (hnever : ∀ publicKey draw, oracle.kemEncaps publicKey draw = none) :
    KemClauses encap byteTrace oracle := by
  refine ⟨?_, ?_, ?_⟩
  · intro publicKey rng draw rest expected _ hsome
    rw [hnever] at hsome
    cases hsome
  · intro publicKey rng error hinv
    rw [hv] at hinv
    rw [hK, if_neg (by simp [hinv])]
  · intro publicKey rng error hcall
    refine ⟨?_, fun draw => hnever _ draw⟩
    rw [hK] at hcall
    rw [hv]
    by_cases hvalid : valid (sliceOf publicKey) = true
    · rw [if_pos hvalid] at hcall
      simp [byteRng] at hcall
    · simpa using hvalid

/-- An oracle whose `kemEncaps` never returns `some` fails the guarded clause as soon as it accepts
one key at a state whose trace has a draw. -/
theorem never_encapsulating_fails_guarded {R : Type}
    (encap : Slice U8 → R → Result (core.result.Result
      (alloc.vec.Vec U8 × Array U8 32#usize) tacenta_boundary.kem.KemError × R))
    (trace : R → List Model.Lifecycle.Key) (oracle : Model.Lifecycle.Oracle)
    (hnever : ∀ publicKey draw, oracle.kemEncaps publicKey draw = none)
    (publicKey : Slice U8) (rng : R) (draw : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key)
    (hvalid : oracle.kemValid (sliceOf publicKey) = true) (htrace : trace rng = draw :: rest) :
    ¬ KemGuardedClause encap trace oracle := by
  intro h
  obtain ⟨_, _, _, _, henc⟩ := h publicKey rng draw rest hvalid htrace
  rw [hnever] at henc
  simp [encapsulationOf, resultOptionOf] at henc

/-- A 1568-byte key, the length the model's KEM accepts. -/
def key1568 : Slice U8 := zeroSlice 1568 (by decide)

theorem kemModelValid_key1568 : kemModelValid (sliceOf key1568) = true := by
  have h : (sliceOf key1568).length = 1568 := by
    simp only [sliceOf, key1568, zeroSlice, List.length_map, List.length_replicate]
  simp only [kemModelValid, h]
  rfl

/-- A byte-stream state holding one draw of 32 zero bytes. -/
def oneDrawState : List U8 := List.replicate 32 0#u8

theorem byteTrace_oneDrawState :
    byteTrace oneDrawState = [List.replicate 32 (0 : UInt8)] := by
  unfold byteTrace oneDrawState
  rw [chunks32, if_pos (by simp), chunks32, if_neg (by simp)]
  simp [Tacenta.SessionUnitBraidT3.u8]

/-- **The guarded clause separates the oracle that never encapsulates.** At the model's
encapsulation, which meets #234's law, an oracle that accepts the model's 1568-byte keys and never
encapsulates meets `OracleOf`'s three KEM clauses and fails the guarded clause. -/
theorem guarded_separates_never_encapsulating :
    ∃ oracle : Model.Lifecycle.Oracle,
      KemClauses (encapModelO byteRng byteCrc) byteTrace oracle ∧
      ¬ KemGuardedClause (encapModelO byteRng byteCrc) byteTrace oracle := by
  let oracle : Model.Lifecycle.Oracle :=
    { oracleM with kemValid := kemModelValid, kemEncaps := fun _ _ => none }
  refine ⟨oracle, never_encapsulating_meets_kemClauses kemModelValid kemModelE
    (encapModelO byteRng byteCrc) (fun _ _ => rfl) oracle rfl (fun _ _ => rfl), ?_⟩
  exact never_encapsulating_fails_guarded _ _ oracle (fun _ _ => rfl) key1568 oneDrawState _ []
    kemModelValid_key1568 byteTrace_oneDrawState

/-! ## The joint model -/

open Tacenta.UnitOracleDh (oracleM_dhPublic one32)

theorem oracleM_kemEncaps : oracleM.kemEncaps = kemEncapsOf kemModelValid kemModelE := rfl
theorem oracleM_kemValid : oracleM.kemValid = kemModelValid := rfl

theorem model_kemDecapsulateClause : KemDecapsulateClause M kemM oracleM :=
  kemDecapsulateClause_of_laws InterpO.model dhM kemM kemModelValid kemModelE signS
    modelO_KemDecapsulate modelO_kemViewInjective

theorem model_sigVerifyClause : SigVerifyClause M dhM oracleM :=
  sigVerifyClause_of_laws InterpO.model dhM kemM kemModelValid kemModelE signS
    modelO_XeddsaVerify modelO_dhViewInjective.2

theorem model_kemGuardedClause :
    KemGuardedClause (InterpO.model.kemEncapsulate byteRng byteCrc) byteTrace oracleM :=
  kemGuardedClause_of_law kemModelValid kemModelE (encapModelO byteRng byteCrc)
    (fun _ _ => rfl) oracleM rfl rfl

theorem u8_ofByte (x : UInt8) : Tacenta.SessionUnitBraidT3.u8 (ofByte x) = x := by
  unfold Tacenta.SessionUnitBraidT3.u8 ofByte
  exact UInt8.ofNat_toNat

theorem map_u8_ofByte (l : Bytes) : (l.map ofByte).map Tacenta.SessionUnitBraidT3.u8 = l := by
  rw [List.map_map]
  conv => rhs; rw [← List.map_id l]
  exact List.map_congr_left (fun x _ => u8_ofByte x)

theorem oracleM_kemDecaps (k : Array U8 32#usize) (c : Slice U8) :
    oracleM.kemDecaps (arrayOf k) (sliceOf c) =
      if c.val.length = 32 then some (sliceOf c) else none := by
  obtain ⟨r, h, hv⟩ := model_kemDecapsulateClause k c
  simp only [M, InterpO.model, decapsModel] at h
  injection h with h
  subst h
  change _ = oracleM.kemDecaps (arrayOf k) (sliceOf c) at hv
  rw [← hv]
  split <;> simp_all [resultOptionOf, arrayOf, sliceOf]

theorem oracleM_sigVerify (pk : Array U8 32#usize) (m : Slice U8) (s : Array U8 64#usize) :
    oracleM.sigVerify (arrayOf pk) (sliceOf m) (arrayOf s) =
      decide (s.val.take 32 = pk.val) := by
  obtain ⟨r, h, hv⟩ := model_sigVerifyClause pk m s
  simp only [M, InterpO.model, verifyModel] at h
  injection h with h
  subst h
  change _ = oracleM.sigVerify (arrayOf pk) (sliceOf m) (arrayOf s) at hv
  rw [← hv]
  split <;> simp_all [verified]

theorem oracleM_sigSign (sk : Array U8 32#usize) (m : Slice U8) (d1 d2 : Bytes)
    (h1 : d1.length = 32) (h2 : d2.length = 32) :
    oracleM.sigSign (arrayOf sk) (sliceOf m) d1 d2 = arrayOf (signS sk m (Slice.new U8)) := by
  have hz : (d1 ++ d2).length ≤ Usize.max := by
    have := Tacenta.SessionUnitSessionT1.small_le_usize_max (n := 64) (by decide)
    simp [h1, h2]; omega
  let z : Slice U8 := ⟨(d1 ++ d2).map ofByte, by simpa using hz⟩
  have hzv : sliceOf z = d1 ++ d2 := map_u8_ofByte _
  show sigSignOf signS (arrayOf sk) (sliceOf m) d1 d2 = _
  unfold sigSignOf
  have hex : (∃ a : Array U8 32#usize, arrayOf a = arrayOf sk) ∧
      (∃ m' : Slice U8, sliceOf m' = sliceOf m) ∧ (∃ z : Slice U8, sliceOf z = d1 ++ d2) :=
    ⟨⟨sk, rfl⟩, ⟨m, rfl⟩, ⟨z, hzv⟩⟩
  rw [dif_pos hex]
  have e1 : hex.1.choose = sk := Tacenta.DispatchEvidenceVacuity.arrayOf_inj hex.1.choose_spec
  rw [e1]
  rfl

/-- The 64-byte array of zeros. -/
def zero64 : Array U8 64#usize := Array.repeat 64#usize 0#u8

/-- **The decapsulation and verification clauses, and the guarded KEM clause, hold at the joint
interpretation, and its KEM and signature are not degenerate.** The KEM accepts a 1568-byte key
and refuses the empty one; at the accepted key `kemEncaps` returns `some` for every draw, so by the
guarded clause the code encapsulates at every state with a draw; the oracle decapsulates what it
encapsulates from a 32-byte draw, with any key pair, and refuses the empty ciphertext; verification
accepts the oracle's signature of any message, from 32-byte draws, under the oracle's public key of
the signing secret, and refuses an all-zero signature under `one32`. -/
theorem kem_sig_clauses_in_model :
    KemDecapsulateClause M kemM oracleM ∧ SigVerifyClause M dhM oracleM ∧
      KemGuardedClause (InterpO.model.kemEncapsulate byteRng byteCrc) byteTrace oracleM ∧
      oracleM.kemValid (sliceOf key1568) = true ∧ oracleM.kemValid [] = false ∧
      (∀ draw, ∃ r, oracleM.kemEncaps (sliceOf key1568) draw = some r) ∧
      (∀ (k : Array U8 32#usize) (publicKey draw : Bytes) (ciphertext secret : Bytes),
        draw.length = 32 → oracleM.kemEncaps publicKey draw = some (ciphertext, secret) →
        oracleM.kemDecaps (arrayOf k) ciphertext = some secret) ∧
      (∀ k : Array U8 32#usize, oracleM.kemDecaps (arrayOf k) [] = none) ∧
      (∀ (sk : Array U8 32#usize) (m : Slice U8) (d1 d2 : Bytes),
        d1.length = 32 → d2.length = 32 →
        oracleM.sigVerify (oracleM.dhPublic (arrayOf sk)) (sliceOf m)
          (oracleM.sigSign (arrayOf sk) (sliceOf m) d1 d2) = true) ∧
      (∀ m : Slice U8, oracleM.sigVerify (arrayOf one32) (sliceOf m) (arrayOf zero64) = false) := by
  refine ⟨model_kemDecapsulateClause, model_sigVerifyClause, model_kemGuardedClause,
    by rw [oracleM_kemValid]; exact kemModelValid_key1568, by rw [oracleM_kemValid]; rfl,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro draw
    rw [oracleM_kemEncaps]
    unfold kemEncapsOf
    rw [if_pos kemModelValid_key1568]
    exact ⟨_, rfl⟩
  · intro k publicKey draw ciphertext secret hlen henc
    rw [oracleM_kemEncaps] at henc
    unfold kemEncapsOf at henc
    split at henc
    · simp only [Option.some.injEq, Prod.mk.injEq] at henc
      obtain ⟨hct, hss⟩ := henc
      let c : Slice U8 := ⟨draw.map ofByte, by
        have := Tacenta.SessionUnitSessionT1.small_le_usize_max (n := 32) (by decide)
        simp [hlen]; omega⟩
      have hc : sliceOf c = draw := map_u8_ofByte draw
      have hct' : ciphertext = draw := by
        rw [← hct]
        simp only [kemModelE, bytesVec32, vecOf]
        rw [← hlen, List.take_length]
        exact map_u8_ofByte draw
      have hss' : secret = draw := by
        rw [← hss]
        simp only [kemModelE, bytesArr32, arrayOf]
        rw [List.take_append_of_le_length (by omega), ← hlen, List.take_length]
        exact map_u8_ofByte draw
      rw [hct', ← hc, oracleM_kemDecaps, if_pos (by simp [c, hlen]), hc, hss']
    · cases henc
  · intro k
    have h := oracleM_kemDecaps k (Slice.new U8)
    rw [if_neg (by simp [Slice.new])] at h
    exact h
  · intro sk m d1 d2 h1 h2
    rw [oracleM_sigSign sk m d1 d2 h1 h2, oracleM_dhPublic, oracleM_sigVerify]
    simp [signS, sk.property]
  · intro m
    rw [oracleM_sigVerify]
    decide

end Tacenta.UnitOracleKemSig

/-! ## Pins

The axiom list and the statement of each result, held by the build. `attest.py` requires them
(`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`). -/

/--
info: 'Tacenta.UnitOracleKemSig.oracleOfGuarded_iff_shape' depends on axioms: [propext,
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
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleKemSig.oracleOfGuarded_iff_shape

/--
info: @Tacenta.UnitOracleKemSig.oracleOfGuarded_iff_shape : ∀ {R : Type} (rc : rand_core_1.RngCore R)
  (crc : rand_core_1.CryptoRng R) (dh : DhView) (kem : KemView) (trace : R → List Model.Lifecycle.Key)
  (oracle : Model.Lifecycle.Oracle),
  Tacenta.UnitOracleKemSig.OracleOfGuarded rc crc dh kem trace oracle ↔
    OracleOfShape InterpO.real rc crc (dhViewOf dh) (kemViewOf kem) trace oracle ∧
      Tacenta.UnitOracleKemSig.KemGuardedClause (InterpO.real.kemEncapsulate rc crc) trace oracle
-/
#guard_msgs in
#check @Tacenta.UnitOracleKemSig.oracleOfGuarded_iff_shape

/--
info: 'Tacenta.UnitOracleKemSig.kemGuardedClause_of_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleKemSig.kemGuardedClause_of_law

/--
info: Tacenta.UnitOracleKemSig.kemGuardedClause_of_law : ∀ (valid : Bytes → Bool)
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
          Tacenta.UnitOracleKemSig.KemGuardedClause encap Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracle
-/
#guard_msgs in
#check @Tacenta.UnitOracleKemSig.kemGuardedClause_of_law

/--
info: 'Tacenta.UnitOracleKemSig.kemClauses_of_guarded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleKemSig.kemClauses_of_guarded

/--
info: @Tacenta.UnitOracleKemSig.kemClauses_of_guarded : ∀ {R : Type}
  (encap :
    Slice U8 →
      R → Result (core.result.Result (alloc.vec.Vec U8 × Std.Array U8 32#usize) tacenta_boundary.kem.KemError × R))
  (trace : R → List Model.Lifecycle.Key) (oracle : Model.Lifecycle.Oracle),
  Tacenta.UnitOracleKemSig.KemGuardedClause encap trace oracle →
    (∀ (publicKey : Slice U8) (rng : R) (error : tacenta_boundary.kem.KemError),
        oracle.kemValid (sliceOf publicKey) = false → encap publicKey rng = ok (core.result.Result.Err error, rng)) →
      (∀ (publicKey : Slice U8) (rng : R) (error : tacenta_boundary.kem.KemError),
          encap publicKey rng = ok (core.result.Result.Err error, rng) →
            oracle.kemValid (sliceOf publicKey) = false ∧
              ∀ (draw : Model.Lifecycle.Key), oracle.kemEncaps (sliceOf publicKey) draw = none) →
        Tacenta.UnitLifecycleIntegrationScreen.KemClauses encap trace oracle
-/
#guard_msgs in
#check @Tacenta.UnitOracleKemSig.kemClauses_of_guarded

/--
info: 'Tacenta.UnitOracleKemSig.never_encapsulating_meets_kemClauses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleKemSig.never_encapsulating_meets_kemClauses

/--
info: Tacenta.UnitOracleKemSig.never_encapsulating_meets_kemClauses : ∀ (valid : Bytes → Bool)
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
        (∀ (publicKey : Model.Lifecycle.Bytes) (draw : Model.Lifecycle.Key), oracle.kemEncaps publicKey draw = none) →
          Tacenta.UnitLifecycleIntegrationScreen.KemClauses encap Tacenta.UnitLifecycleIntegrationScreen.byteTrace
            oracle
-/
#guard_msgs in
#check @Tacenta.UnitOracleKemSig.never_encapsulating_meets_kemClauses

/--
info: 'Tacenta.UnitOracleKemSig.never_encapsulating_fails_guarded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleKemSig.never_encapsulating_fails_guarded

/--
info: @Tacenta.UnitOracleKemSig.never_encapsulating_fails_guarded : ∀ {R : Type}
  (encap :
    Slice U8 →
      R → Result (core.result.Result (alloc.vec.Vec U8 × Std.Array U8 32#usize) tacenta_boundary.kem.KemError × R))
  (trace : R → List Model.Lifecycle.Key) (oracle : Model.Lifecycle.Oracle),
  (∀ (publicKey : Model.Lifecycle.Bytes) (draw : Model.Lifecycle.Key), oracle.kemEncaps publicKey draw = none) →
    ∀ (publicKey : Slice U8) (rng : R) (draw : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
      oracle.kemValid (sliceOf publicKey) = true →
        trace rng = draw :: rest → ¬Tacenta.UnitOracleKemSig.KemGuardedClause encap trace oracle
-/
#guard_msgs in
#check @Tacenta.UnitOracleKemSig.never_encapsulating_fails_guarded

/--
info: 'Tacenta.UnitOracleKemSig.guarded_separates_never_encapsulating' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleKemSig.guarded_separates_never_encapsulating

/--
info: Tacenta.UnitOracleKemSig.guarded_separates_never_encapsulating : ∃ oracle,
  Tacenta.UnitLifecycleIntegrationScreen.KemClauses
      (encapModelO Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc)
      Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracle ∧
    ¬Tacenta.UnitOracleKemSig.KemGuardedClause
        (encapModelO Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc)
        Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracle
-/
#guard_msgs in
#check @Tacenta.UnitOracleKemSig.guarded_separates_never_encapsulating

/--
info: 'Tacenta.UnitOracleKemSig.kem_sig_clauses_in_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleKemSig.kem_sig_clauses_in_model

/--
info: Tacenta.UnitOracleKemSig.kem_sig_clauses_in_model : KemDecapsulateClause M kemM oracleM ∧
  SigVerifyClause M dhM oracleM ∧
    Tacenta.UnitOracleKemSig.KemGuardedClause
        (InterpO.model.kemEncapsulate Tacenta.UnitLifecycleIntegrationScreen.byteRng
          Tacenta.UnitLifecycleIntegrationScreen.byteCrc)
        Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracleM ∧
      oracleM.kemValid (sliceOf Tacenta.UnitOracleKemSig.key1568) = true ∧
        oracleM.kemValid [] = false ∧
          (∀ (draw : Model.Lifecycle.Key),
              ∃ r, oracleM.kemEncaps (sliceOf Tacenta.UnitOracleKemSig.key1568) draw = some r) ∧
            (∀ (k : Std.Array U8 32#usize) (publicKey draw ciphertext secret : Bytes),
                List.length draw = 32 →
                  oracleM.kemEncaps publicKey draw = some (ciphertext, secret) →
                    oracleM.kemDecaps (arrayOf k) ciphertext = some secret) ∧
              (∀ (k : Std.Array U8 32#usize), oracleM.kemDecaps (arrayOf k) [] = none) ∧
                (∀ (sk : Std.Array U8 32#usize) (m : Slice U8) (d1 d2 : Bytes),
                    List.length d1 = 32 →
                      List.length d2 = 32 →
                        oracleM.sigVerify (oracleM.dhPublic (arrayOf sk)) (sliceOf m)
                            (oracleM.sigSign (arrayOf sk) (sliceOf m) d1 d2) =
                          true) ∧
                  ∀ (m : Slice U8),
                    oracleM.sigVerify (arrayOf Tacenta.UnitOracleDh.one32) (sliceOf m)
                        (arrayOf Tacenta.UnitOracleKemSig.zero64) =
                      false
-/
#guard_msgs in
#check @Tacenta.UnitOracleKemSig.kem_sig_clauses_in_model

/--
info: def Tacenta.UnitOracleKemSig.KemGuardedClause : {R : Type} →
  (Slice U8 →
      R → Result (core.result.Result (alloc.vec.Vec U8 × Std.Array U8 32#usize) tacenta_boundary.kem.KemError × R)) →
    (R → List Model.Lifecycle.Key) → Model.Lifecycle.Oracle → Prop :=
fun {R} encap trace oracle =>
  ∀ (publicKey : Slice U8) (rng : R) (draw : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
    oracle.kemValid (sliceOf publicKey) = true →
      trace rng = draw :: rest →
        ∃ result rng',
          encap publicKey rng = ok (core.result.Result.Ok result, rng') ∧
            trace rng' = rest ∧
              encapsulationOf (core.result.Result.Ok result) = oracle.kemEncaps (sliceOf publicKey) draw
-/
#guard_msgs in
#print Tacenta.UnitOracleKemSig.KemGuardedClause

/--
info: structure Tacenta.UnitOracleKemSig.OracleOfGuarded {R : Type} (rngCore : rand_core_1.RngCore R)
  (cryptoRng : rand_core_1.CryptoRng R) (dh : DhView) (kem : KemView) (trace : R → List Model.Lifecycle.Key)
  (oracle : Model.Lifecycle.Oracle) : Prop
number of parameters: 7
parents:
  Tacenta.UnitOracleKemSig.OracleOfGuarded.toOracleOf : OracleOf rngCore cryptoRng dh kem trace oracle
fields:
  Tacenta.UnitLifecycleT3.OracleOf.dhPublic : ∀ (secret : tacenta_boundary.dh.PrivateKey),
      ∃ publicKey, secret.public_key = ok publicKey ∧ dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret)
  Tacenta.UnitLifecycleT3.OracleOf.dhAgree : ∀ (secret : tacenta_boundary.dh.PrivateKey)
      (publicKey : tacenta_boundary.dh.PublicKeyBytes),
      ∃ result,
        secret.agree publicKey = ok result ∧
          Option.map arrayOf result = oracle.dhAgree (dh.privateKey secret) (dh.publicKey publicKey)
  Tacenta.UnitLifecycleT3.OracleOf.identityValid : ∀ (publicKey : tacenta_boundary.dh.PublicKeyBytes),
      ∃ result, is_valid_identity_key publicKey = ok result ∧ result = oracle.identityValid (dh.publicKey publicKey)
  Tacenta.UnitLifecycleT3.OracleOf.aeadSeal : ∀ (key1 key2 : Std.Array U8 32#usize) (iv : Std.Array U8 16#usize)
      (ad plaintext : Slice U8),
      ∃ ciphertext,
        tacenta_boundary.aead.encrypt key1 key2 iv ad plaintext = ok ciphertext ∧
          vecOf ciphertext = oracle.aeadSeal (arrayOf key1) (arrayOf key2) (arrayOf iv) (sliceOf ad) (sliceOf plaintext)
  Tacenta.UnitLifecycleT3.OracleOf.aeadOpen : ∀ (key1 key2 : Std.Array U8 32#usize) (iv : Std.Array U8 16#usize)
      (ciphertext associatedData : Slice U8),
      ∃ result,
        tacenta_boundary.aead.decrypt key1 key2 iv ciphertext associatedData = ok result ∧
          resultOptionOf vecOf result =
            oracle.aeadOpen (arrayOf key1) (arrayOf key2) (arrayOf iv) (sliceOf ciphertext) (sliceOf associatedData)
  Tacenta.UnitLifecycleT3.OracleOf.kemEncapsulateSuccess : ∀ (publicKey : Slice U8) (rng : R)
      (draw : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key)
      (expected : Model.Lifecycle.Bytes × Model.Lifecycle.Key),
      trace rng = draw :: rest →
        oracle.kemEncaps (sliceOf publicKey) draw = some expected →
          ∃ result rng',
            tacenta_boundary.kem.encapsulate rngCore cryptoRng publicKey rng = ok (core.result.Result.Ok result, rng') ∧
              trace rng' = rest ∧ encapsulationOf (core.result.Result.Ok result) = some expected
  Tacenta.UnitLifecycleT3.OracleOf.kemInvalidKey : ∀ (publicKey : Slice U8) (rng : R)
      (error : tacenta_boundary.kem.KemError),
      oracle.kemValid (sliceOf publicKey) = false →
        tacenta_boundary.kem.encapsulate rngCore cryptoRng publicKey rng = ok (core.result.Result.Err error, rng)
  Tacenta.UnitLifecycleT3.OracleOf.kemEncapsulateError : ∀ (publicKey : Slice U8) (rng : R)
      (error : tacenta_boundary.kem.KemError),
      tacenta_boundary.kem.encapsulate rngCore cryptoRng publicKey rng = ok (core.result.Result.Err error, rng) →
        oracle.kemValid (sliceOf publicKey) = false ∧
          ∀ (draw : Model.Lifecycle.Key), oracle.kemEncaps (sliceOf publicKey) draw = none
  Tacenta.UnitLifecycleT3.OracleOf.kemDecapsulate : ∀ (keyPair : tacenta_boundary.kem.KeyPair) (ciphertext : Slice U8),
      ∃ result,
        tacenta_boundary.kem.decapsulate keyPair ciphertext = ok result ∧
          resultOptionOf arrayOf result = oracle.kemDecaps (kem.keyPair keyPair) (sliceOf ciphertext)
  Tacenta.UnitLifecycleT3.OracleOf.sigVerify : ∀ (publicKey : tacenta_boundary.dh.PublicKeyBytes) (message : Slice U8)
      (signature : Std.Array U8 64#usize),
      ∃ result,
        tacenta_boundary.xeddsa.verify publicKey message signature = ok result ∧
          verified result = oracle.sigVerify (dh.publicKey publicKey) (sliceOf message) (arrayOf signature)
  Tacenta.UnitLifecycleT3.OracleOf.sigSign : ∀ (secret : Std.Array U8 32#usize) (message : Slice U8) (rng : R)
      (draw1 draw2 : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
      trace rng = draw1 :: draw2 :: rest →
        ∃ signature rng',
          tacenta_boundary.xeddsa.sign rngCore cryptoRng secret message rng = ok (signature, rng') ∧
            trace rng' = rest ∧ arrayOf signature = oracle.sigSign (arrayOf secret) (sliceOf message) draw1 draw2
  Tacenta.UnitLifecycleT3.OracleOf.random32 : ∀ (rng : R) (draw : Model.Lifecycle.Key)
      (rest : List Model.Lifecycle.Key),
      trace rng = draw :: rest →
        ∃ value rng',
          lifecycle.random_secret rngCore cryptoRng rng = ok (value, rng') ∧ arrayOf value = draw ∧ trace rng' = rest
  Tacenta.UnitOracleKemSig.OracleOfGuarded.kemEncapsulateGuarded : ∀ (publicKey : Slice U8) (rng : R)
      (draw : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
      oracle.kemValid (sliceOf publicKey) = true →
        trace rng = draw :: rest →
          ∃ result rng',
            tacenta_boundary.kem.encapsulate rngCore cryptoRng publicKey rng = ok (core.result.Result.Ok result, rng') ∧
              trace rng' = rest ∧
                encapsulationOf (core.result.Result.Ok result) = oracle.kemEncaps (sliceOf publicKey) draw
constructor:
  Tacenta.UnitOracleKemSig.OracleOfGuarded.mk {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R} {dh : DhView} {kem : KemView} {trace : R → List Model.Lifecycle.Key}
    {oracle : Model.Lifecycle.Oracle} (toOracleOf : OracleOf rngCore cryptoRng dh kem trace oracle)
    (kemEncapsulateGuarded :
      ∀ (publicKey : Slice U8) (rng : R) (draw : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
        oracle.kemValid (sliceOf publicKey) = true →
          trace rng = draw :: rest →
            ∃ result rng',
              tacenta_boundary.kem.encapsulate rngCore cryptoRng publicKey rng =
                  ok (core.result.Result.Ok result, rng') ∧
                trace rng' = rest ∧
                  encapsulationOf (core.result.Result.Ok result) = oracle.kemEncaps (sliceOf publicKey) draw) :
    Tacenta.UnitOracleKemSig.OracleOfGuarded rngCore cryptoRng dh kem trace oracle
field notation resolution order:
  Tacenta.UnitOracleKemSig.OracleOfGuarded, Tacenta.UnitLifecycleT3.OracleOf
-/
#guard_msgs in
#print Tacenta.UnitOracleKemSig.OracleOfGuarded
