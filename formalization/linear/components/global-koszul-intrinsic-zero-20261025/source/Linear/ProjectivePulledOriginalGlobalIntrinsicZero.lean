module
public import Linear.ProjectivePulledOriginalChartDataCutZero
public import Linear.ProjectivePulledOriginalChartInternalExtSupport
public import Linear.SchemeModuleGlobalKoszulIntrinsicZero
public import Linear.ProjectivePulledWholeCokernelLambdaStatement
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
  nativeProjectiveKoszulTerm projectivePulledLinearKoszulForms projectivePulledLinearKoszulComplex
  projectivePulledWholeCutResolutionTarget projectivePulledOriginalNamedExactChart
  schemeModuleGlobalKoszulIntrinsicZeroStatement
variable {n p : ℕ}
/-- Statement only:the SAME actual GLOBAL original Ext class is zero iff
its ORIGINAL top coefficient morphism has zero genuine
pullback to the original nonreduced affine cut. ALL quasicoherent
coefficients and functionals are included. -/
def projectivePulledOriginalGlobalIntrinsicZeroStatement
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin ((p+1)+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin ((p+1)+1) → ℂ) (k : ℤ)
    (e : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      cokernel ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0) ≅
        projectivePulledWholeCutResolutionTarget f V L hL w k)
    (he : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      QuasiIso (originalChainCokernelTargetAugmentation
        (projectivePulledLinearKoszulComplex f V L hL w k)
        (projectivePulledWholeCutResolutionTarget f V L hL w k) e)) : Prop :=
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  schemeModuleGlobalKoszulIntrinsicZeroStatement
    (projectivePulledLinearKoszulComplex f V L hL w k) p
    (projectivePulledOriginalNamedExactChart f V L hL w k)
    (originalChainCokernelTargetAugmentation (projectivePulledLinearKoszulComplex f V L hL w k)
      (projectivePulledWholeCutResolutionTarget f V L hL w k) e) he
    (projectivePulledOriginalKoszul_isZero_above f V L hL w k (p+2) (by omega))
/-- The original ambient cover DERIVES internal-Ext support;the actual
source iso transfers canonical-lambda injectivity from the original
cokernel to the SAME whole-cut target. Both cover and cokernel-lambda
bijectivity are derived in the final common-parameter family. -/
theorem projectivePulledOriginalGlobalIntrinsicZeroStatement_proof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin ((p+1)+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin ((p+1)+1) → ℂ) (k : ℤ)
    (e : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      cokernel ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0) ≅
        projectivePulledWholeCutResolutionTarget f V L hL w k)
    (he : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      QuasiIso (originalChainCokernelTargetAugmentation
        (projectivePulledLinearKoszulComplex f V L hL w k)
        (projectivePulledWholeCutResolutionTarget f V L hL w k) e))
    (hc : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      ∀ x : Proj (homogeneousQuotientPiece V.ideal.toIdeal),
        x ∈ Proj.basicOpen (homogeneousQuotientPiece V.ideal.toIdeal)
          (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)) ∨
        ∃ i : Fin (p+1),x ∈ Proj.basicOpen (homogeneousQuotientPiece V.ideal.toIdeal)
          (projectivePulledLinearKoszulForms f V L w i))
    (hLambda : projectivePulledOriginalCokernelLambdaStatement f V L hL w k) :
    projectivePulledOriginalGlobalIntrinsicZeroStatement f V L hL w k e he := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  apply schemeModuleGlobalKoszulIntrinsicZeroProof_of_cokernelLambda _ _ _ _ _ _ e
  · intro N _ q v
    exact projectivePulledOriginalKoszulInternalExt_succ f V L hL w k q N v
  · exact fun N => hLambda N p
  · exact projectivePulledOriginalChartInternalExtSupportStatement_proof f V L hL w k hc e
end LinearStudy
