module
public import Linear.ProjectivePulledOriginalChartPresentation
public import Linear.MappedChainPresentationAugmentation
public import Linear.ProjectivePulledWholeCutResolutionObjects
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading nativeProjectiveKoszulComplex
  nativeProjectiveKoszulTerm projectivePulledLinearKoszulForms
  projectivePulledLinearKoszulComplex projectivePulledWholeCutResolutionTarget
  projectivePulledOriginalChartPresentationData nativeProjectiveKoszulMappedPresentationData
variable {n r : ℕ}

/-- Explicit STATEMENT of the SAME original whole-cut augmentation's
ACTUAL X0 chart square. Transport the original cokernel target witness
ONLY through the PROVED equality of the payload source and original C.
Every chart/quotient map is constructed;this Prop alone is not a proof. -/
def projectivePulledOriginalChartAugmentationLaw
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ)
    (e : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      cokernel ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0) ≅
        projectivePulledWholeCutResolutionTarget f V L hL w k) : Prop :=
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI := originalProjectiveZeroChart_isOpenImmersion V
  letI := schemeModuleOpenRestriction_additive (originalProjectiveZeroChart V)
  letI := schemeModuleOpenRestriction_preservesHomology (originalProjectiveZeroChart V)
  let d := projectivePulledOriginalChartPresentationData f V L hL w k
  let ce := eqToIso (congrArg
    (fun C : ChainComplex (Proj (homogeneousQuotientPiece V.ideal.toIdeal)).Modules ℕ => cokernel (C.d 1 0))
    (projectivePulledOriginalChartPresentationData_source f V L hL w k))
  mappedOriginalChainCokernelAugmentationChartLaw (Scheme.Modules.restrictFunctor (originalProjectiveZeroChart V))
    d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2
    (projectivePulledWholeCutResolutionTarget f V L hL w k) (ce ≪≫ e)

/-- PROVE the SAME actual original whole-cut augmentation's chart square.
No desired square or new geometric hypothesis is an input. The actual
original Setup produces e,on its one nonempty parameter open. -/
theorem projectivePulledOriginalChartAugmentationLaw_proof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ)
    (e : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      cokernel ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0) ≅
        projectivePulledWholeCutResolutionTarget f V L hL w k) :
    projectivePulledOriginalChartAugmentationLaw f V L hL w k e := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI := originalProjectiveZeroChart_isOpenImmersion V
  letI := schemeModuleOpenRestriction_additive (originalProjectiveZeroChart V)
  letI := schemeModuleOpenRestriction_preservesHomology (originalProjectiveZeroChart V)
  let d := projectivePulledOriginalChartPresentationData f V L hL w k
  have h := mappedChainPresentationAugmentationLaw_proof
    (Scheme.Modules.restrictFunctor (originalProjectiveZeroChart V)) d
  exact h (projectivePulledWholeCutResolutionTarget f V L hL w k)
    (eqToIso (congrArg
      (fun C : ChainComplex (Proj (homogeneousQuotientPiece V.ideal.toIdeal)).Modules ℕ => cokernel (C.d 1 0))
      (projectivePulledOriginalChartPresentationData_source f V L hL w k)) ≪≫ e)

end LinearStudy
