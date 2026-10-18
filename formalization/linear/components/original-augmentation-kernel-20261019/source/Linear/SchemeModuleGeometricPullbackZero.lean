module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Additive
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
/-- For the ACTUAL sheaf pullback/pushforward adjunction,a morphism
vanishes after geometric pullback iff its SAME original adjoint unit
composite vanishes. No flatness,closedness or faithfulness is assumed. -/
theorem schemeModule_pullback_map_zero_iff_unit
    {X Y : Scheme.{u}} (f : Y ⟶ X) {A B : X.Modules} (a : A ⟶ B) :
    a ≫ (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app B = 0 ↔
      (Scheme.Modules.pullback f).map a = 0 := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have h : adj.homEquiv A ((Scheme.Modules.pullback f).obj B)
      ((Scheme.Modules.pullback f).map a) = a ≫ adj.unit.app B := by
    rw [Adjunction.homEquiv_unit]
    exact (adj.unit.naturality a).symm
  constructor
  · intro hz
    apply (adj.homEquiv A ((Scheme.Modules.pullback f).obj B)).injective
    rw [h,hz,adj.homAddEquiv_zero]
  · intro hz
    rw [← h,hz,adj.homAddEquiv_zero]
end LinearStudy
