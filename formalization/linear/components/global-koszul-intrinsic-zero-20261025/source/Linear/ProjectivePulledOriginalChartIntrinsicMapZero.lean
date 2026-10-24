module
public import Linear.ProjectivePulledOriginalNamedExactChart
public import Linear.SchemeModuleOpenKoszulIntrinsicZero
public import Linear.ProjectivePulledOriginalKoszulInternalExtVanishing
public import Linear.ProjectivePulledOriginalKoszulAboveRank
public import Linear.ProjectivePulledWholeCutResolutionObjects
public import Linear.ChainActualCokernelTargetAugmentation
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
  schemeModuleOpenKoszulIntrinsicMapZeroStatement
variable {n p : ℕ}
/-- STATEMENT ONLY. On the SAME actual original X0 chart,the SAME canonical
lambda class vanishes iff the ORIGINAL top coefficient MORPHISM itself pulls
back to zero on the SAME original nonreduced cut. ALL quasicoherent
coefficients and ALL original functionals are included. -/
def projectivePulledOriginalChartIntrinsicMapZeroStatement
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
  schemeModuleOpenKoszulIntrinsicMapZeroStatement
    (projectivePulledLinearKoszulComplex f V L hL w k) p
    (projectivePulledOriginalNamedExactChart f V L hL w k)
    (originalChainCokernelTargetAugmentation (projectivePulledLinearKoszulComplex f V L hL w k)
      (projectivePulledWholeCutResolutionTarget f V L hL w k) e) he
    (projectivePulledOriginalKoszul_isZero_above f V L hL w k (p+2) (by omega))
/-- PROOF:derive all source SHEAF Ext vanishings from the
actual original Koszul terms. Original Setup must supply its e and he. -/
theorem projectivePulledOriginalChartIntrinsicMapZeroStatement_proof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin ((p+1)+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin ((p+1)+1) → ℂ) (k : ℤ)
    (e : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      cokernel ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0) ≅
        projectivePulledWholeCutResolutionTarget f V L hL w k)
    (he : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      QuasiIso (originalChainCokernelTargetAugmentation
        (projectivePulledLinearKoszulComplex f V L hL w k)
        (projectivePulledWholeCutResolutionTarget f V L hL w k) e)) :
    projectivePulledOriginalChartIntrinsicMapZeroStatement f V L hL w k e he := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  apply schemeModuleOpenKoszulIntrinsicMapZeroProof
  intro N _ q v
  exact projectivePulledOriginalKoszulInternalExt_succ f V L hL w k q N v
end LinearStudy
