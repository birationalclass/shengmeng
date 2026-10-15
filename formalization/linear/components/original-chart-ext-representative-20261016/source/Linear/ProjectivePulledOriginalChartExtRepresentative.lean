module
public import Linear.StandardMappedChainPresentationNamedExt
public import Linear.ProjectivePulledOriginalChartPresentation
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
  nativeProjectiveKoszulTerm projectivePulledLinearKoszulForms projectivePulledLinearKoszulComplex
  projectivePulledWholeCutResolutionTarget projectivePulledOriginalChartPresentationData
  nativeProjectiveKoszulMappedPresentationData standardMappedChainPresentationNamedExtLaw
  mappedChainPresentationNamedExtLaw
variable {n r : ℕ}

/-- Explicit STATEMENT of the SAME original global quotient-roof's actual
X0 chart representative,with the original named complex and top functional.
The actual chart payload/source equality/target comparison are constructed.
The original augmentation's quasiiso is explicit here and the original
Setup derives it on ONE NONEMPTY open before ALL integer twists. -/
def projectivePulledOriginalChartExtRepresentativeLaw
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
  standardMappedChainPresentationNamedExtLaw
    (Scheme.Modules.restrictFunctor (originalProjectiveZeroChart V))
    (projectivePulledOriginalChartPresentationData f V L hL w k)
    (projectivePulledLinearKoszulComplex f V L hL w k)
    (projectivePulledOriginalChartPresentationData_source f V L hL w k)
    (projectivePulledWholeCutResolutionTarget f V L hL w k) e

/-- PROVE the actual original X0 chart representative equality from the
constructed quotient square and native Ext action. No desired class
identity,square,source equality or new geometry certificate is assumed. -/
theorem projectivePulledOriginalChartExtRepresentativeLaw_proof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ)
    (e : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      cokernel ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0) ≅
        projectivePulledWholeCutResolutionTarget f V L hL w k) :
    projectivePulledOriginalChartExtRepresentativeLaw f V L hL w k e := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI := originalProjectiveZeroChart_isOpenImmersion V
  letI := schemeModuleOpenRestriction_additive (originalProjectiveZeroChart V)
  letI := schemeModuleOpenRestriction_preservesHomology (originalProjectiveZeroChart V)
  exact standardMappedChainPresentationNamedExtLaw_proof
    (Scheme.Modules.restrictFunctor (originalProjectiveZeroChart V))
    (projectivePulledOriginalChartPresentationData f V L hL w k)
    (projectivePulledLinearKoszulComplex f V L hL w k)
    (projectivePulledOriginalChartPresentationData_source f V L hL w k)
    (projectivePulledWholeCutResolutionTarget f V L hL w k) e

end LinearStudy
