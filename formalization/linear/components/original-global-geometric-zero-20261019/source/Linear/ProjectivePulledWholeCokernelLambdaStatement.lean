module
public import Linear.ProjectivePulledWholeCutResolutionObjects
public import Linear.ProjectivePulledLinearKoszulGlobal
public import Linear.SchemeModuleFiniteSupportLambdaSourceIso
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading projectivePulledLinearKoszulComplex
  nativeProjectiveModuleSheaf
variable {n r : ℕ}
/-- Statement definition only: canonical lambda is bijective for the SAME actual original Koszul d1-cokernel, all actual coefficient sheaves and positive degrees. -/
def projectivePulledOriginalCokernelLambdaStatement
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ) : Prop :=
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  ∀ N : (Proj (homogeneousQuotientPiece V.ideal.toIdeal)).Modules, ∀ j : ℕ,
    Function.Bijective (schemeModuleGlobalToInternalExt
      (cokernel ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0)) N j)
/-- Given ACTUAL Artinian structure and ACTUAL source identification,the previous canonical source-naturality theorem transfers the proved lambda comparison. These geometric inputs are derived from original hypotheses in the family. -/
theorem projectivePulledOriginalCokernelLambdaStatement_proof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ)
    (hA : IsArtinianScheme (projectivePulledLinearSectionScheme f V L hL w))
    (e : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      cokernel ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0) ≅
        projectivePulledWholeCutResolutionTarget f V L hL w k) :
    projectivePulledOriginalCokernelLambdaStatement f V L hL w k := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI : IsArtinianScheme (projectivePulledLinearSectionScheme f V L hL w) := hA
  letI : IsClosedImmersion (projectivePulledLinearSectionClosedEmbedding f V L hL w) :=
    projectivePulledLinearSectionClosedEmbedding_isClosedImmersion f V L hL w
  intro N j
  apply schemeModuleGlobalToInternalExt_bijective_of_sourceIso e N j
  unfold projectivePulledWholeCutResolutionTarget
  exact schemeModuleGlobalToInternalExt_artinianClosedImmersion_bijective
    (projectivePulledLinearSectionClosedEmbedding f V L hL w) _ N j
end LinearStudy
