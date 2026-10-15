module
public import Linear.NativeProjectiveKoszulChartModuleExt
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
attribute [local irreducible] nativeProjectiveKoszulChartModuleExtLaw
  tildeKoszulMappedOriginalModuleExtLaw homogeneousQuotientGrading nativeProjectiveKoszulComplex
  nativeProjectiveKoszulTerm projectivePulledLinearKoszulForms
  CategoryTheory.Functor.mapHomologicalComplex
variable {n r : ℕ}

/-- After splitting through the native graded-chart boundary,keep the
actual original specialization small. Explicit STATEMENT for the SAME original X0 chart and whole-cut
augmentation. Positive MODULE exactness and the actual module Ext class
are derived. An actual coefficient iso is explicit at this general
boundary;the original top-term frame is constructed separately. -/
def projectivePulledOriginalChartModuleExtLaw
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ)
    (e : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      cokernel ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0) ≅
        projectivePulledWholeCutResolutionTarget f V L hL w k) : Prop :=
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  nativeProjectiveKoszulChartModuleExtLaw (homogeneousQuotientPiece V.ideal.toIdeal)
    (fun t : Fin (n+1) => Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X t))
    (fun t => ⟨MvPolynomial.X t,MvPolynomial.isHomogeneous_X ℂ t,rfl⟩)
    (homogeneousQuotient_coordinate_adjoin_eq_top V.ideal.toIdeal)
    (projectivePulledLinearKoszulForms f V L w)
    (projectivePulledLinearKoszulForms_homogeneous f V L hL w) k
    (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩
    (projectivePulledWholeCutResolutionTarget f V L hL w k) e

/-- Prove the SAME original class/MODULE representative comparison from
constructed original maps,without a desired Ext equality,source exactness
or module representative supplied as an extra geometric premise. -/
theorem projectivePulledOriginalChartModuleExtLaw_proof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ)
    (e : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      cokernel ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0) ≅
        projectivePulledWholeCutResolutionTarget f V L hL w k) :
    projectivePulledOriginalChartModuleExtLaw f V L hL w k e := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  exact nativeProjectiveKoszulChartModuleExtLaw_proof (homogeneousQuotientPiece V.ideal.toIdeal)
    (fun t : Fin (n+1) => Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X t))
    (fun t => ⟨MvPolynomial.X t,MvPolynomial.isHomogeneous_X ℂ t,rfl⟩)
    (homogeneousQuotient_coordinate_adjoin_eq_top V.ideal.toIdeal)
    (projectivePulledLinearKoszulForms f V L w)
    (projectivePulledLinearKoszulForms_homogeneous f V L hL w) k
    (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩
    (projectivePulledWholeCutResolutionTarget f V L hL w k) e

end LinearStudy
