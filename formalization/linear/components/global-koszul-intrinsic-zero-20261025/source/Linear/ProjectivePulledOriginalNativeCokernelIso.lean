module
public import Linear.ProjectivePulledOriginalNamedExactChart
public import Linear.ProjectivePulledWholeCutResolutionObjects
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
variable {n r : ℕ}
/-- Actual source iso,only unfolding the original complex name ONCE.
No source/target object is replaced and no desired Ext result is input. -/
def projectivePulledOriginalNativeCokernelIso
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ)
    (e : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      cokernel ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0) ≅
        projectivePulledWholeCutResolutionTarget f V L hL w k) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    cokernel ((nativeProjectiveKoszulComplex (homogeneousQuotientPiece V.ideal.toIdeal)
      (projectivePulledLinearKoszulForms f V L w)
      (projectivePulledLinearKoszulForms_homogeneous f V L hL w) k).d 1 0) ≅
      projectivePulledWholeCutResolutionTarget f V L hL w k := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  exact e
end LinearStudy
