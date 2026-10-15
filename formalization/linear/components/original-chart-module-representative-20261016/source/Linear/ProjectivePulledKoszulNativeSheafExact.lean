module
public import Linear.ProjectivePulledKoszulNativeChartExact
public import Linear.ProjectivePulledLinearKoszulAffineStandard
public import Linear.TildeComplexExact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading projectivePulledLinearKoszulForms
  nativeProjectiveKoszulOnAffine nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm
  projectivePulledLinearKoszulStandardAffineIso koszulComplex
variable {n r : ℕ}

/-- Under the FULL original f,V,L hypotheses,derive positive exactness
of the SAME actual original GLOBAL Koszul restricted to the native X0 chart,
for ALL integer twists,on a nonempty parameter open independent of k.
This proves exactness ON THIS CHART;whole global exactness is separate. -/
theorem projectivePulledLinearSection_exists_nativeChartSheafKoszul_exactAt
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
        let R := CommRingCat.of (HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal) a)
        let ι := Proj.awayι (homogeneousQuotientPiece V.ideal.toIdeal) a ha one_pos
        ∀ k : ℤ,∀ p : ℕ,0 < p →
          (nativeProjectiveKoszulOnAffine (homogeneousQuotientPiece V.ideal.toIdeal) R ι
            (projectivePulledLinearKoszulForms f V L w)
            (projectivePulledLinearKoszulForms_homogeneous f V L hL w) k).ExactAt p := by
  obtain ⟨c,hc,hex,hgood⟩ := projectivePulledLinearSection_exists_nativeChartKoszul_exactAt
    f V hproper hq hf hV L hL hinj hfinite hdim x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  dsimp only
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let a := Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)
  let ha : a ∈ homogeneousQuotientPiece V.ideal.toIdeal 1 :=
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩
  let R := CommRingCat.of (HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal) a)
  intro k p hp
  have he := hgood w hw p hp
  have ht := tilde_chainComplex_exactAt R _ p he
  exact ht.of_iso (projectivePulledLinearKoszulStandardAffineIso f V L hL w k a ha).symm

end LinearStudy
