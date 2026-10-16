module
public import Linear.ProjectivePulledOriginalChainWholeCutExtClass
public import Linear.OriginalChainStandardSourceBoundaryStatement
public import Linear.SchemeModuleDerivedInternalHom
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

/-- SAME original geometric Koszul epsilon equals the ACTUAL iterated native
source boundary. This is a statement definition;the next theorem proves it.
Actual e and he are derived from the original Setup in the final family. -/
def projectivePulledOriginalWholeCutSourceBoundaryStatement
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
  originalChainStandardSourceBoundaryStatement
    (projectivePulledLinearKoszulComplex f V L hL w k) r
    (originalChainCokernelTargetAugmentation (projectivePulledLinearKoszulComplex f V L hL w k)
      (projectivePulledWholeCutResolutionTarget f V L hL w k) e) he
    (projectivePulledOriginalKoszulTopTwistIso f V L hL w k).hom
    (projectivePulledOriginalKoszulTopFunctional_isCocycle f V L hL w k _)


theorem projectivePulledOriginalWholeCutSourceBoundaryStatement_proof
    (hr : 0 < r)
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
    projectivePulledOriginalWholeCutSourceBoundaryStatement f V L hL w k e he := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  exact originalChainStandardSourceBoundaryStatement_proof
    (projectivePulledLinearKoszulComplex f V L hL w k) r hr
    (originalChainCokernelTargetAugmentation (projectivePulledLinearKoszulComplex f V L hL w k)
      (projectivePulledWholeCutResolutionTarget f V L hL w k) e) he
    (projectivePulledOriginalKoszulTopTwistIso f V L hL w k).hom
    (projectivePulledOriginalKoszulTopFunctional_isCocycle f V L hL w k _)


end LinearStudy
