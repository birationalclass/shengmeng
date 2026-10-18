module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
/-- Actual image opens agree under proved chart-ring equality and proved
heterogeneous equality of the actual inclusions. Pure chart geometry;
no internal-Ext functor or restriction-adjunction unit is evaluated. -/
theorem scheme_chart_image_top_eq_of_HEq
    {X : Scheme.{u}} {R S : CommRingCat.{u}}
    (j : Spec R ⟶ X) [IsOpenImmersion j] (l : Spec S ⟶ X) [IsOpenImmersion l] (hR : R = S) (hj : HEq j l) :
    j ''ᵁ ⊤ = l ''ᵁ ⊤ := by
  cases hR
  have h : j = l := eq_of_heq hj
  subst l
  rfl
end LinearStudy
