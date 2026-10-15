module
public import Linear.NativeKoszulOriginalQuotientAugmentationProof
public import Linear.ProjectivePulledWholeCutNativeAugmentationConditions
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading projectivePulledLinearKoszulForms
  nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm
  nativeProjectiveKoszulMappedPresentationData CategoryTheory.Functor.mapHomologicalComplex
variable {n r : ℕ}

/-- Specialize ORIGINAL f,V,L,w,X0 and degree-q forms while the final
geometric target and its comparison remain universally quantified.
The SAME native projection formula is proved, and its source-target
equality is obtained from the original constructed presentation. -/
def projectivePulledLinearKoszulOriginalQuotientAugmentationProof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ)
    (hc : projectivePulledLinearKoszulAmbientCover f V L w) :=
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  nativeProjectiveKoszulOriginalQuotientAugmentationProof
    (homogeneousQuotientPiece V.ideal.toIdeal)
    (fun t : Fin (n+1) => Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X t))
    (fun t => ⟨MvPolynomial.X t,MvPolynomial.isHomogeneous_X ℂ t,rfl⟩)
    (homogeneousQuotient_coordinate_adjoin_eq_top V.ideal.toIdeal)
    (projectivePulledLinearKoszulForms f V L w)
    (projectivePulledLinearKoszulForms_homogeneous f V L hL w) k
    (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩ hc

end LinearStudy
