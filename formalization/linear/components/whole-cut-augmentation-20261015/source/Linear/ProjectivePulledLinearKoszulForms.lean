module
public import Linear.ProjectiveSectionDefiningForms
public import Linear.HomogeneousCoordinateGrading
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n r : ℕ}
/-- ORIGINAL degree-q pulled linear forms in the ORIGINAL homogeneous
coordinate ring of V. No affine replacement or radicalization is used. -/
def projectivePulledLinearKoszulForms (f : HomogeneousEndomorphism n)
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (w : Fin (r+1) → ℂ) : Fin r → (CoordinateRing n ⧸ V.ideal.toIdeal) :=
  fun i => Ideal.Quotient.mk V.ideal.toIdeal
    (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))

/-- The ORIGINAL forms' homogeneous degree is proved from the ORIGINAL
endomorphism and degree-one L; it is not an additional grading assumption. -/
theorem projectivePulledLinearKoszulForms_homogeneous (f : HomogeneousEndomorphism n)
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1) (w : Fin (r+1) → ℂ) (i : Fin r) :
    projectivePulledLinearKoszulForms f V L w i ∈
      homogeneousQuotientPiece V.ideal.toIdeal f.degree :=
  ⟨_, projective_pulled_back_section_forms_homogeneous f L hL w i, rfl⟩

end LinearStudy
