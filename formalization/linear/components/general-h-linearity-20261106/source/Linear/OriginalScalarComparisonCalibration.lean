module
public import Mathlib.Logic.Function.Basic
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
universe u v w x y
/-- Compose two proved actual scalar calibrations with a proved chart scalar square. -/
theorem originalScalarComparison_of_calibrations
    {A : Type u} {B : Type v} {C : Type w} {M : Type x} {N : Type y}
    (e : M → N) (actA : A → M → M) (actB : B → N → N)
    (sigmaA : C → A) (sigmaB : C → B) (z : C) (a : A) (b : B) (m : M)
    (ha : a=sigmaA z) (hb : b=sigmaB z)
    (h : e (actA (sigmaA z) m)=actB (sigmaB z) (e m)) :
    e (actA a m)=actB b (e m) := by
  cases ha
  cases hb
  exact h
end LinearStudy
