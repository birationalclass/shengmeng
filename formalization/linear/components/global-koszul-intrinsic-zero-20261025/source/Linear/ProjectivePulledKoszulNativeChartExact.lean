module
public import Linear.ProjectivePulledKoszulChartExactTransfer
public import Linear.ProjectiveCutAffineKoszul
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading projectivePulledLinearKoszulForms koszulComplex
variable {n r : ℕ}

/-- From ALL original f,V,L hypotheses,DERIVE a nonempty parameter open
where the SAME original native-Away Koszul has positive exactness.
The source exactness and chart/numerator comparison are PROVED outputs,
not additional hypotheses;no global CM/free/flat condition is imposed. -/
theorem projectivePulledLinearSection_exists_nativeChartKoszul_exactAt
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hproper : V.ideal.toIdeal ≠ ⊥)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) = (r : WithBot ℕ∞))
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ c : MvPolynomial (Fin (r+1)) ℂ,c ≠ 0 ∧
      (∃ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0) ∧
      ∀ w : Fin (r+1) → ℂ,MvPolynomial.eval w c ≠ 0 →
        letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
        let a := Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)
        let ha : a ∈ homogeneousQuotientPiece V.ideal.toIdeal 1 :=
          ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩
        ∀ j : ℕ,0 < j →
          (koszulComplex (Fintype.linearCombination
            (HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal) a)
            (fun i : Fin r => HomogeneousLocalization.Away.mk
              (homogeneousQuotientPiece V.ideal.toIdeal) ha f.degree
              (projectivePulledLinearKoszulForms f V L w i)
              (by simpa using projectivePulledLinearKoszulForms_homogeneous f V L hL w i)))).ExactAt j := by
  obtain ⟨c,hc,hex,hgood⟩ := projectivePulledLinearSection_exists_affineKoszul_exactAt
    f V hproper hq hf hV L hL hinj hfinite hdim x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  dsimp only
  intro j hj
  obtain ⟨_,_,_,_,_,he⟩ := hgood w hw
  exact projectivePulledKoszul_nativeChart_exactAt_of_affine f V L hL w j (he j hj)

end LinearStudy
