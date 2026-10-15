module
public import Linear.ProjectivePulledLinearKoszulGlobal
public import Linear.NativeGlobalKoszulAffineCounit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading nativeProjectiveKoszulComplex
  nativeProjectiveKoszulTerm projectivePulledLinearKoszulForms
variable {n r : ℕ}

/-- The actual affine complex used in the comparison is EXACTLY the
restriction of the SAME named ORIGINAL f,V,L,w global Koszul complex.
This is proved from the original definitions,not supplied as a certificate. -/
theorem projectivePulledLinearKoszulComplex_restrict_eq
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ) (R : CommRingCat) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    (j : Spec R ⟶ Proj (homogeneousQuotientPiece V.ideal.toIdeal)) →
    [IsOpenImmersion j] →
    letI := schemeModuleOpenRestriction_additive j
    ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (projectivePulledLinearKoszulComplex f V L hL w k) =
    nativeProjectiveKoszulOnAffine (homogeneousQuotientPiece V.ideal.toIdeal) R j
      (projectivePulledLinearKoszulForms f V L w)
      (projectivePulledLinearKoszulForms_homogeneous f V L hL w) k := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  intro j hj
  letI := hj
  letI := schemeModuleOpenRestriction_additive j
  unfold projectivePulledLinearKoszulComplex nativeProjectiveKoszulOnAffine
  rfl

end LinearStudy
