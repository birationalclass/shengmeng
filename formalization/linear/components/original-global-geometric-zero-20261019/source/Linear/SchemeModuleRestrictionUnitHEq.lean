module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
/-- Transfer the ACTUAL adjunction unit property along proved equal chart
schemes and proved heterogeneously equal inclusions. No Ext comparison,
coefficient identification or source-complex reduction is involved. -/
theorem schemeModule_restrictionUnit_isIso_of_chartHEq
    {X : Scheme.{u}} {R S : CommRingCat.{u}} (j : Spec R ⟶ X) [IsOpenImmersion j]
    (l : Spec S ⟶ X) [IsOpenImmersion l] (hR : R = S) (hj : HEq j l)
    (B : X.Modules) (hu : IsIso ((Scheme.Modules.restrictAdjunction l).unit.app B)) :
    IsIso ((Scheme.Modules.restrictAdjunction j).unit.app B) := by
  cases hR
  have h : j = l := eq_of_heq hj
  subst l
  exact hu
end LinearStudy
