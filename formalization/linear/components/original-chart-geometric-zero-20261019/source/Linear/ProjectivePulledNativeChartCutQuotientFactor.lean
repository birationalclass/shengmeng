module
public import Linear.HomogeneousQuotientNativeChartFactorNaturality
public import Linear.RingEquivOriginalQuotientFactor
public import Linear.ProjectiveCutKoszulQuotient
public import Linear.ProjectivePulledLinearKoszulForms
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading
variable {n r : ℕ}

/-- The SAME original native chart cut quotient is the first native chart
of the WHOLE original homogeneous cut. Construct both coordinate maps and
PROVE compatibility with the ORIGINAL quotient map on EVERY element.
No radicalization, reducedness, finite-cut or avoidance assumption. -/
theorem projectivePulledLinearSection_nativeChart_exists_quotient_factor_equiv
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) :
    let J := projectivePulledLinearSectionIdeal f V L w
    let hJ := projectivePulledLinearSectionIdeal_isHomogeneous f V L hL w
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    letI := homogeneousQuotientGrading J hJ
    let a := Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)
    let ha : a ∈ homogeneousQuotientPiece V.ideal.toIdeal 1 :=
      ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩
    let h : Fin r → Away (homogeneousQuotientPiece V.ideal.toIdeal) a := fun i =>
      Away.mk (homogeneousQuotientPiece V.ideal.toIdeal) ha f.degree
        (projectivePulledLinearKoszulForms f V L w i)
        (by simpa using projectivePulledLinearKoszulForms_homogeneous f V L hL w i)
    ∃ e : ((Away (homogeneousQuotientPiece V.ideal.toIdeal) a) ⧸
        Ideal.span (Set.range h)) ≃+*
        Away (homogeneousQuotientPiece J) (Ideal.Quotient.mk J (MvPolynomial.X 0)),
      ∀ x, e (Ideal.Quotient.mk _ x) =
        Away.map (homogeneousQuotientFactorGraded V.ideal.toIdeal J le_sup_left) a x := by
  let J := projectivePulledLinearSectionIdeal f V L w
  let hJ := projectivePulledLinearSectionIdeal_isHomogeneous f V L hL w
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI := homogeneousQuotientGrading J hJ
  let a := Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)
  let ha : a ∈ homogeneousQuotientPiece V.ideal.toIdeal 1 :=
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩
  let h : Fin r → Away (homogeneousQuotientPiece V.ideal.toIdeal) a := fun i =>
    Away.mk (homogeneousQuotientPiece V.ideal.toIdeal) ha f.degree
      (projectivePulledLinearKoszulForms f V L w i)
      (by simpa using projectivePulledLinearKoszulForms_homogeneous f V L hL w i)
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let C := MvPolynomial (Fin n) ℂ ⧸ J.map (affineChartPolynomialMap (K := ℂ)).toRingHom
  let b : Fin r → B := fun i => Ideal.Quotient.mk V.affineIdeal
    (affineChartPolynomialMap (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)))
  obtain ⟨eI,eJ,heI,heJ,hn⟩ := homogeneousQuotient_nativeChart_exists_factor_compatible
    V.ideal.toIdeal J V.ideal.isHomogeneous hJ le_sup_left
  have hh : eI ∘ b = h := by
    funext i
    simpa only [Function.comp_apply,b,h,homogeneousQuotientNativeChartElement,
      projectivePulledLinearKoszulForms,IntegralProjectiveEquations.affineIdeal] using
      heI f.degree (MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i))
        (projective_pulled_back_section_forms_homogeneous f L hL w i)
  have hmap : (Ideal.span (Set.range b)).map eI.toRingHom = Ideal.span (Set.range h) := by
    rw [Ideal.map_span,← Set.range_comp']
    change Ideal.span (Set.range (eI ∘ b)) = Ideal.span (Set.range h)
    exact congrArg (fun v => Ideal.span (Set.range v)) hh
  let eQ : (B ⧸ Ideal.span (Set.range b)) ≃+* C :=
    (projectivePulledLinearSection_koszulQuotientAlgEquiv f V L w).toRingEquiv
  let g : B →+* C := Ideal.Quotient.factor (Ideal.map_mono (show V.ideal.toIdeal ≤ J from le_sup_left))
  have hQ (x : B) : eQ (Ideal.Quotient.mk _ x) = g x := by
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
    exact projectivePulledLinearSection_koszulQuotientAlgEquiv_mk f V L w p
  let u := Away.map (homogeneousQuotientFactorGraded V.ideal.toIdeal J le_sup_left) a
  refine ⟨ringEquivOriginalQuotientFactor (Ideal.span (Set.range b))
    (Ideal.span (Set.range h)) eI eJ eQ hmap.symm,?_⟩
  intro x
  exact ringEquivOriginalQuotientFactor_mk _ _ eI eJ eQ hmap.symm g u hQ hn x

end LinearStudy