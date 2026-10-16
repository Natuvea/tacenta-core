/-
Model.LifecycleFrame: which fields of the lifecycle oracle `decrypt` reads.

`Model.Lifecycle.decrypt` takes a whole `Oracle`, which also carries the
identity rule, the AEAD seal, the KEM and the signing primitives. This module
shows, from the definitions alone, that `decrypt` reads five fields of it:
`draws`, `braidKem`, `dhPublic`, `dhAgree` and `aeadOpen`. Two oracles that
agree on those five give the same session, the same result and the same
remaining draws on every state and message; the oracle each run returns is its
own input oracle with only `draws` changed.

It adds lemmas only. No definition of `Model.Lifecycle` is changed, and the
module sits beside `Model/Lifecycle.lean` rather than in it so that file stays
as it was.
-/
import Model.Lifecycle

namespace Model.Lifecycle

/-- `dispatchDecrypt` reads only the oracle's `dhAgree` (through the repeat
    test). -/
theorem dispatchDecrypt_oracle_frame (oracle oracle' : Oracle) (session : Session)
    (message : Bytes) (hagree : oracle'.dhAgree = oracle.dhAgree) :
    dispatchDecrypt oracle' session message = dispatchDecrypt oracle session message := by
  obtain ⟨d, k, p, a, i, s, o, kv, ke, kd, sv, ss⟩ := oracle
  obtain ⟨d', k', p', a', i', s', o', kv', ke', kd', sv', ss'⟩ := oracle'
  simp only at hagree
  subst hagree
  rfl

/-- `decryptRatchet` reads only `draws`, `braidKem`, `dhPublic`, `dhAgree` and
    `aeadOpen`: on an oracle that agrees with another on those fields it returns
    the other's step with its own oracle, carrying the same remaining draws. -/
theorem decryptRatchet_oracle_frame (view : CodewordView) (oracle oracle' : Oracle)
    (session : Session) (message : Bytes)
    (hdraws : oracle'.draws = oracle.draws) (hkem : oracle'.braidKem = oracle.braidKem)
    (hpublic : oracle'.dhPublic = oracle.dhPublic) (hagree : oracle'.dhAgree = oracle.dhAgree)
    (hopen : oracle'.aeadOpen = oracle.aeadOpen) :
    decryptRatchet view oracle' session message =
      { decryptRatchet view oracle session message with
        oracle := { oracle' with
          draws := (decryptRatchet view oracle session message).oracle.draws } } := by
  obtain ⟨d, k, p, a, i, s, o, kv, ke, kd, sv, ss⟩ := oracle
  obtain ⟨d', k', p', a', i', s', o', kv', ke', kd', sv', ss'⟩ := oracle'
  simp only at hdraws hkem hpublic hagree hopen
  subst hdraws hkem hpublic hagree hopen
  unfold decryptRatchet random32 takeDraw
  by_cases hf : agreementFailed session = true
  · simp only [hf, if_true]
  · simp only [hf, if_false, Bool.false_eq_true]
    cases hd : CompositeHeader.decodeDetailed message with
    | error reason => rfl
    | ok decoded =>
        obtain ⟨composite, ciphertext⟩ := decoded
        simp only
        cases hr : a' session.ratchetPrivate composite.dh with
        | none => rfl
        | some dhOutRecv =>
            simp only
            cases d' with
            | nil => rfl
            | cons draw rest =>
                simp only
                cases hs : a' draw composite.dh with
                | none => rfl
                | some dhOutSend =>
                    simp only
                    split
                    · rfl
                    · split <;> rfl

/-- **`decrypt` reads only `draws`, `braidKem`, `dhPublic`, `dhAgree` and
    `aeadOpen`.** Two oracles that agree on those five fields give, on every
    codeword view, state and message, the same step up to the oracle it
    returns, and that returned oracle is the run's own input oracle with the
    same remaining draws. So the identity rule, the AEAD seal, the KEM
    validity, encapsulation and decapsulation, and the signing primitives are
    not read by `decrypt`. -/
theorem decrypt_oracle_frame (view : CodewordView) (oracle oracle' : Oracle)
    (session : Session) (message : Bytes)
    (hdraws : oracle'.draws = oracle.draws) (hkem : oracle'.braidKem = oracle.braidKem)
    (hpublic : oracle'.dhPublic = oracle.dhPublic) (hagree : oracle'.dhAgree = oracle.dhAgree)
    (hopen : oracle'.aeadOpen = oracle.aeadOpen) :
    decrypt view oracle' session message =
      { decrypt view oracle session message with
        oracle := { oracle' with
          draws := (decrypt view oracle session message).oracle.draws } } := by
  have hdispatch := dispatchDecrypt_oracle_frame oracle oracle' session message hagree
  unfold decrypt
  rw [hdispatch]
  split
  · obtain ⟨d, k, p, a, i, s, o, kv, ke, kd, sv, ss⟩ := oracle
    obtain ⟨d', k', p', a', i', s', o', kv', ke', kd', sv', ss'⟩ := oracle'
    simp only at hdraws
    subst hdraws
    rfl
  · next inner _ =>
    rw [decryptRatchet_oracle_frame view oracle oracle' session inner hdraws hkem hpublic hagree
      hopen]
    generalize decryptRatchet view oracle session inner = step
    obtain ⟨stepSession, stepResult, stepOracle⟩ := step
    cases stepResult <;> rfl

end Model.Lifecycle
