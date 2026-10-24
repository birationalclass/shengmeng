module
public import Linear.ProjectivePulledOriginalExactChartData
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading nativeProjectiveKoszulComplex
  nativeProjectiveKoszulTerm projectivePulledLinearKoszulForms
  projectivePulledOriginalExactChartData schemeModuleOpenKoszulChartData
variable {n r : ℕ}
/-- Same actual native chart with the source explicitly the NAMED original
Koszul complex. This is DATA only;the one source alias is unfolded without
transporting or rebuilding any dependent ring,inclusion or equation field. -/
def projectivePulledOriginalNamedExactChart
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    schemeModuleOpenKoszulChartData (projectivePulledLinearKoszulComplex f V L hL w k) r := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  unfold projectivePulledLinearKoszulComplex
  exact projectivePulledOriginalExactChartData f V L hL w k
end LinearStudy
