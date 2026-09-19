import Translation.UnitLifecycleT1
import Translation.SessionUnitBraidT1

/-!
# Public Session lifecycle T1 proofs

The eviction retry is proved in `UnitLifecycleT1` without importing the Braid
proof package, whose local stepping configuration intentionally differs from
the wire proofs in that module. This file composes those already checked
layers for the five public lifecycle entry points.
-/

namespace Tacenta.UnitLifecycleT1

open Aeneas Aeneas.Std Result
open tacenta_session_unit

@[step]
theorem agreement_failed_no_panic (self : lifecycle.Session) :
    lifecycle.Session.agreement_failed self ⦃ fun _ => True ⦄ := by
  unfold lifecycle.Session.agreement_failed
  exact Tacenta.SessionUnitBraidT1.Braid.failed_no_panic self.braid

@[step]
theorem message_keys_no_panic
    (hkdf : Tacenta.SessionUnitT1.HkdfTotal)
    (hza : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
    (mk : Array U8 32#usize) (labels : tacenta_ratchet.LabelSet) :
    tacenta_ratchet.message_keys mk labels ⦃ fun _ => True ⦄ := by
  unfold tacenta_ratchet.message_keys
  step
  simp_all only
  step
  simp_all only
  step with Tacenta.SessionUnitT1.hkdf_step hkdf 80#usize
    (Array.to_slice (Array.repeat 32#usize 0#u8)) (Array.to_slice mk)
    tacenta_ratchet.MK_INFO (by scalar_tac)
  step with Tacenta.SessionUnitBraidT1.zeroizing_new_spec hza a1
  step
  step with Tacenta.SessionUnitBraidT1.zeroizing_deref_spec out_post
  step*
  all_goals simp_all

end Tacenta.UnitLifecycleT1
