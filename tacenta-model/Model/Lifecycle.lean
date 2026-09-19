/-
Model.Lifecycle: executable orchestration for the public session operations.

This first slice fixes the primitive boundary and its randomness discipline.
The lifecycle functions consume `draws` from the head and return the oracle
with the unused suffix. Every primitive result is a function of the complete
argument list passed at the boundary. The later refinement relation can
therefore say that Rust and the model made the same call, rather than merely
that they happened to receive the same result.

The primitive algorithms are deliberately outside this model. The theorem is
intended to quantify over every oracle; real-crypto vectors instantiate one.
-/
import Model.PersistedState

namespace Model.Lifecycle

abbrev Bytes := List UInt8
abbrev Key := Model.State.Key
abbrev Iv := Bytes

/-- Results supplied by the trusted primitive boundary.

    `draws` is ordered. Operations that need randomness consume its head and
    return the oracle containing its tail. `kemEncaps` and `sigSign` take that
    draw explicitly, so using the wrong draw or calling them in the wrong order
    changes the model result. -/
structure Oracle where
  draws : List Key
  dhPublic : Key → Key
  dhAgree : Key → Key → Option Key
  aeadSeal : Key → Key → Iv → Bytes → Bytes → Bytes
  aeadOpen : Key → Key → Iv → Bytes → Bytes → Option Bytes
  kemEncaps : Bytes → Key → Option (Bytes × Key)
  kemDecaps : Bytes → Bytes → Option Key
  sigVerify : Key → Bytes → Bytes → Bool
  sigSign : Key → Bytes → Key → Bytes

/-- Consume one named 32-byte random draw. Exhaustion is a model refusal rather
    than an invented value; callers decide which public refusal it maps to. -/
def takeDraw (oracle : Oracle) : Option (Key × Oracle) :=
  match oracle.draws with
  | [] => none
  | draw :: rest => some (draw, { oracle with draws := rest })

@[simp] theorem takeDraw_empty (oracle : Oracle) (h : oracle.draws = []) :
    takeDraw oracle = none := by
  simp [takeDraw, h]

@[simp] theorem takeDraw_cons (oracle : Oracle) (draw : Key) (rest : List Key)
    (h : oracle.draws = draw :: rest) :
    takeDraw oracle = some (draw, { oracle with draws := rest }) := by
  simp [takeDraw, h]

/-- Consuming a draw changes no primitive interpretation. This is the small
    frame fact used whenever an operation threads the remaining trace onward. -/
theorem takeDraw_keeps_dhPublic (oracle oracle' : Oracle) (draw : Key)
    (h : takeDraw oracle = some (draw, oracle')) :
    oracle'.dhPublic = oracle.dhPublic := by
  cases hd : oracle.draws with
  | nil => simp [takeDraw, hd] at h
  | cons head tail =>
      simp only [takeDraw, hd, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]

end Model.Lifecycle
