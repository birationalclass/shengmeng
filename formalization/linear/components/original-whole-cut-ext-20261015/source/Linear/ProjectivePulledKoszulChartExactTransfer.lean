module
public import Linear.KoszulRingEquivExact
public import Linear.HomogeneousQuotientNativeChart
public import Linear.ProjectivePulledLinearKoszulForms
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading projectivePulledLinearKoszulForms
variable {n r : ℕ}

/-- Transfer the actual ORIGINAL affine-coordinate Koszul exactness to the
SAME original native degree-zero chart ring and SAME H_i/X0^q fractions.
The chart ring isomorphism and numerator compatibility are DERIVED. -/
theorem projectivePulledKoszul_nativeChart_exactAt_of_affine
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (j : ℕ)
    (h : (koszulComplex (Fintype.linearCombination
      (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
      (fun i : Fin r => Ideal.Quotient.mk V.affineIdeal
        (affineChartPolynomialMap
          (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))))).ExactAt j) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let a := Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)
    let ha : a ∈ homogeneousQuotientPiece V.ideal.toIdeal 1 :=
      ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩
    (koszulComplex (Fintype.linearCombination
      (HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal) a)
      (fun i : Fin r => HomogeneousLocalization.Away.mk
        (homogeneousQuotientPiece V.ideal.toIdeal) ha f.degree
        (projectivePulledLinearKoszulForms f V L w i)
        (by simpa using projectivePulledLinearKoszulForms_homogeneous f V L hL w i)))).ExactAt j := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let a := Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)
  let ha : a ∈ homogeneousQuotientPiece V.ideal.toIdeal 1 :=
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩
  let H : Fin r → (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) :=
    fun i => Ideal.Quotient.mk V.affineIdeal
      (affineChartPolynomialMap (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))
  obtain ⟨e,he⟩ := homogeneousQuotient_nativeChart_ringEquiv
    V.ideal.toIdeal V.ideal.isHomogeneous
  have hh : e ∘ H =
      (fun i : Fin r => HomogeneousLocalization.Away.mk
        (homogeneousQuotientPiece V.ideal.toIdeal) ha f.degree
        (projectivePulledLinearKoszulForms f V L w i)
        (by simpa using projectivePulledLinearKoszulForms_homogeneous f V L hL w i)) := by
    funext i
    simpa only [Function.comp_apply,H,homogeneousQuotientNativeChartElement,
      projectivePulledLinearKoszulForms,IntegralProjectiveEquations.affineIdeal] using
      he f.degree (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))
        (projective_pulled_back_section_forms_homogeneous f L hL w i)
  have ht := functionKoszul_exactAt_ringEquiv e H j h
  rw [hh] at ht
  exact ht

end LinearStudy
