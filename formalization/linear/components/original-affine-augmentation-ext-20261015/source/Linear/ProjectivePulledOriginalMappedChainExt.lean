module
public import Linear.ProjectivePulledOriginalKoszulTopBoundary
public import Linear.SchemeModuleOriginalMappedChainExt
public import Linear.OriginalProjectiveZeroChart
public import Linear.ChainActualCokernelTargetAugmentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading nativeProjectiveKoszulComplex
  nativeProjectiveKoszulTerm nativeProjectiveModuleSheaf projectivePulledLinearKoszulForms
  projectivePulledLinearKoszulComplex projectivePulledWholeCutResolutionTarget
  projectivePulledKoszulTopResolutionTarget
variable {n r : ℕ}

/-- The actual original X0 restriction equality,with SAME global original
complex,target,quotient augmentation and top exterior functional;the right
side is now the class of the SAME actual restricted CHAIN complex. This
names a mathematical STATEMENT,not a proof or a new assumption. -/
def projectivePulledOriginalMappedChainExtLaw
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ)
    (e : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      cokernel ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0) ≅
        projectivePulledWholeCutResolutionTarget f V L hL w k)
    (he : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      QuasiIso (originalChainCokernelTargetAugmentation
        (projectivePulledLinearKoszulComplex f V L hL w k)
        (projectivePulledWholeCutResolutionTarget f V L hL w k) e)) : Prop :=
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI := originalProjectiveZeroChart_isOpenImmersion V
  schemeModuleOriginalMappedChainExtLaw (originalProjectiveZeroChart V)
    (projectivePulledLinearKoszulComplex f V L hL w k) r
    (originalChainCokernelTargetAugmentation (projectivePulledLinearKoszulComplex f V L hL w k)
      (projectivePulledWholeCutResolutionTarget f V L hL w k) e) he
    (projectivePulledOriginalKoszulTopTwistIso f V L hL w k).hom
    (projectivePulledOriginalKoszulTopFunctional_isCocycle f V L hL w k _)

/-- Prove that actual restriction law using exact native open restriction.
The actual original X0 chart is constructed and proved open; the CHAIN-class equality
is derived rather than supplied. Internal sheaf Ext remains separate. -/
theorem projectivePulledOriginalMappedChainExtLaw_proof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ)
    (e : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      cokernel ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0) ≅
        projectivePulledWholeCutResolutionTarget f V L hL w k)
    (he : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      QuasiIso (originalChainCokernelTargetAugmentation
        (projectivePulledLinearKoszulComplex f V L hL w k)
        (projectivePulledWholeCutResolutionTarget f V L hL w k) e)) :
    projectivePulledOriginalMappedChainExtLaw f V L hL w k e he := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI := originalProjectiveZeroChart_isOpenImmersion V
  exact schemeModuleOriginalMappedChainExtLaw_proof (originalProjectiveZeroChart V)
    (projectivePulledLinearKoszulComplex f V L hL w k) r
    (originalChainCokernelTargetAugmentation (projectivePulledLinearKoszulComplex f V L hL w k)
      (projectivePulledWholeCutResolutionTarget f V L hL w k) e) he
    (projectivePulledOriginalKoszulTopTwistIso f V L hL w k).hom
    (projectivePulledOriginalKoszulTopFunctional_isCocycle f V L hL w k _)

end LinearStudy