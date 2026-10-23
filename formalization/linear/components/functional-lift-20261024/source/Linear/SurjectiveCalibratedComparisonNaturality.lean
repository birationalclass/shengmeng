module
public import Mathlib.Logic.Function.Basic
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
/-- Naturality of a calibrated comparison follows from the TWO original
coefficient squares on a surjective common chart. No target naturality is assumed. -/
theorem surjectiveCalibratedComparison_naturality
    {X Y A B C D : Type*} (qA : X → A) (qB : X → B) (qC : Y → C) (qD : Y → D)
    (eA : A → B) (eC : C → D) (f : X → Y) (u : A → C) (v : B → D)
    (hqA : Function.Surjective qA)
    (hA : ∀ x,eA (qA x)=qB x) (hC : ∀ y,eC (qC y)=qD y)
    (hu : ∀ x,u (qA x)=qC (f x)) (hv : ∀ x,v (qB x)=qD (f x)) (a : A) :
    eC (u a) = v (eA a) := by
  obtain ⟨x,rfl⟩ := hqA a
  rw [hu,hC,hA,hv]
end LinearStudy
