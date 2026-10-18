module
public import Linear.HomogeneousQuotientOriginalCutCover
public import Linear.ProjectivePulledSectionNativeCoverage
public import Linear.ProjectivePulledLinearKoszulForms
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading projectivePulledLinearKoszulForms
variable {n r : ℕ}

/-- From the ORIGINAL geometric assumptions,derive a nonempty parameter
open covering EVERY actual original V-prime by X0!=0 or some ORIGINAL
pulled equation H_i!=0. This is coverage of V itself,not only its closed
complex points or the Proj of a replacement radical ideal. -/
theorem projectivePulledLinearSection_exists_original_ambient_cover
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ c : MvPolynomial (Fin (r+1)) ℂ,c ≠ 0 ∧
      (∃ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0) ∧
      ∀ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0 →
        letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
        ∀ x : Proj (homogeneousQuotientPiece V.ideal.toIdeal),
          x ∈ Proj.basicOpen (homogeneousQuotientPiece V.ideal.toIdeal)
            (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)) ∨
          ∃ i : Fin r,x ∈ Proj.basicOpen (homogeneousQuotientPiece V.ideal.toIdeal)
            (projectivePulledLinearKoszulForms f V L w i) := by
  obtain ⟨c,hc,hex,hgood⟩ := projectivePulledLinearSection_exists_chart_avoidance_open
    f V hq hf hV L hL hinj hfinite x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  unfold projectivePulledLinearKoszulForms
  apply homogeneousQuotient_chart_or_original_equation V.ideal.toIdeal V.ideal.isHomogeneous
    (fun i => MvPolynomial.aeval f.forms (projectiveLinearSectionForms L w i)) (MvPolynomial.X 0)
  intro v hv hva
  by_contra hvne
  exact ((hgood w hw).2.2.2 v hv hvne).1 (by simpa using hva)

end LinearStudy