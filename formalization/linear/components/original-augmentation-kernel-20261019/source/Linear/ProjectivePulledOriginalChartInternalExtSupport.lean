module
public import Linear.ProjectivePulledOriginalTargetOffCutZero
public import Linear.ProjectivePulledOriginalNamedChartImage
public import Linear.SchemeModuleChartInternalExtCover
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
  nativeProjectiveKoszulTerm projectivePulledLinearKoszulForms projectivePulledWholeCutResolutionTarget
  schemeModuleChartInternalExtSupportStatement projectivePulledOriginalNamedExactChart
variable {n r : ℕ}
/-- Statement only:the SAME original chart and whole-cut target.
All coefficients and degrees are packaged by the generic support law. -/
def projectivePulledOriginalChartInternalExtSupportStatement
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ) : Prop :=
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  schemeModuleChartInternalExtSupportStatement
    (projectivePulledLinearKoszulComplex f V L hL w k) r
    (projectivePulledOriginalNamedExactChart f V L hL w k)
    (projectivePulledWholeCutResolutionTarget f V L hL w k)
/-- Derive support from actual original coverage and the same source e.
The generic chart-identity theorem keeps the concrete package opaque. -/
theorem projectivePulledOriginalChartInternalExtSupportStatement_proof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ)
    (hc : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      ∀ x : Proj (homogeneousQuotientPiece V.ideal.toIdeal),
        x ∈ Proj.basicOpen (homogeneousQuotientPiece V.ideal.toIdeal)
          (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)) ∨
        ∃ i : Fin r,x ∈ Proj.basicOpen (homogeneousQuotientPiece V.ideal.toIdeal)
          (projectivePulledLinearKoszulForms f V L w i))
    (e : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      cokernel ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0) ≅
        projectivePulledWholeCutResolutionTarget f V L hL w k) :
    projectivePulledOriginalChartInternalExtSupportStatement f V L hL w k := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  exact schemeModuleChartInternalExtSupportStatement_of_originalCover
    (projectivePulledLinearKoszulComplex f V L hL w k) r
    (projectivePulledOriginalNamedExactChart f V L hL w k)
    (projectivePulledWholeCutResolutionTarget f V L hL w k)
    (fun i : Fin r => Proj.basicOpen (homogeneousQuotientPiece V.ideal.toIdeal)
      (projectivePulledLinearKoszulForms f V L w i))
    (fun x => by
      rw [projectivePulledOriginalNamedExactChart_image f V L hL w k]
      exact hc x)
    (fun i => projectivePulledOriginalTargetOffCutZeroProof f V L hL w k e i)
end LinearStudy
