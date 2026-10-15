module
public import Linear.NativeKoszulMappedPresentationData
public import Linear.OriginalProjectiveZeroChart
public import Linear.HomogeneousQuotientKoszulAffineCounit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading nativeProjectiveKoszulComplex
  nativeProjectiveKoszulTerm projectivePulledLinearKoszulForms
  CategoryTheory.Functor.mapHomologicalComplex
variable {n r : ℕ}

/-- Construct the ACTUAL original X0 presentation payload,including the
SAME whole Koszul complex,actual chart complex/iso,original quotient
cofork and its proved colimit. No desired augmentation square is a field. -/
def projectivePulledOriginalChartPresentationData
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    letI := originalProjectiveZeroChart_isOpenImmersion V
    letI := schemeModuleOpenRestriction_additive (originalProjectiveZeroChart V)
    mappedChainPresentationData (Scheme.Modules.restrictFunctor (originalProjectiveZeroChart V)) := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI := originalProjectiveZeroChart_isOpenImmersion V
  letI := schemeModuleOpenRestriction_additive (originalProjectiveZeroChart V)
  exact nativeProjectiveKoszulMappedPresentationData (homogeneousQuotientPiece V.ideal.toIdeal)
    (fun t : Fin (n+1) => Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X t))
    (fun t => ⟨MvPolynomial.X t,MvPolynomial.isHomogeneous_X ℂ t,rfl⟩)
    (homogeneousQuotient_coordinate_adjoin_eq_top V.ideal.toIdeal)
    (projectivePulledLinearKoszulForms f V L w)
    (projectivePulledLinearKoszulForms_homogeneous f V L hL w) k
    (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩

/-- The payload source is EXACTLY the SAME named original global Koszul
complex. This equality is proved from the actual construction,not assumed. -/
theorem projectivePulledOriginalChartPresentationData_source
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    letI := originalProjectiveZeroChart_isOpenImmersion V
    letI := schemeModuleOpenRestriction_additive (originalProjectiveZeroChart V)
    (projectivePulledOriginalChartPresentationData f V L hL w k).1 =
      projectivePulledLinearKoszulComplex f V L hL w k := by
  rfl

end LinearStudy
