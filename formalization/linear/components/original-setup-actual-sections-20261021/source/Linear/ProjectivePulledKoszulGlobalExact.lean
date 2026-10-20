module
public import Linear.ProjectivePulledKoszulNativeSheafExact
public import Linear.ProjectivePulledLinearKoszulGlobal
public import Linear.ProjectivePulledKoszulOriginalAmbientCover
public import Linear.NativeKoszulGlobalExactFromChart
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
  koszulComplex
variable {n r : ℕ}

/-- Under ALL ORIGINAL geometric hypotheses in the nonzero-ideal branch,
construct a nonempty parameter open on which the SAME named ORIGINAL
GLOBAL weighted Koszul complex is exact in EVERY positive degree,for ALL
integer twists. The parameter open is chosen BEFORE k. Original X0 chart
exactness and actual ambient coverage are DERIVED,while off-cut exactness
is proved from actual original unit sections and native additive stalks.
No local/global exactness,cover,regular sequence or extra target condition
is an input. This is source exactness;augmentation/epsilon/derived SHEAF
Ext and the original Lemma4.2 remain separate obligations. -/
theorem projectivePulledLinearSection_exists_globalKoszul_exactAt
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
        ∀ k : ℤ,∀ p : ℕ,0 < p →
          (projectivePulledLinearKoszulComplex f V L hL w k).ExactAt p := by
  obtain ⟨a,ha,_,he⟩ := projectivePulledLinearSection_exists_nativeChartSheafKoszul_exactAt
    f V hproper hq hf hV L hL hinj hfinite hdim x0 hx0
  obtain ⟨b,hb,_,hcover⟩ := projectivePulledLinearSection_exists_original_ambient_cover
    f V hq hf hV L hL hinj hfinite x0 hx0
  have hc : a*b ≠ 0 := mul_ne_zero ha hb
  have hex : ∃ w : Fin (r+1) → ℂ,MvPolynomial.eval w (a*b) ≠ 0 := by
    by_contra h
    push Not at h
    apply hc
    apply MvPolynomial.funext
    intro w
    rw [map_zero]
    exact h w
  refine ⟨a*b,hc,hex,?_⟩
  intro w hw k p hp
  rw [map_mul] at hw
  obtain ⟨hwa,hwb⟩ := mul_ne_zero_iff.mp hw
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  change (nativeProjectiveKoszulComplex (homogeneousQuotientPiece V.ideal.toIdeal)
    (projectivePulledLinearKoszulForms f V L w)
    (projectivePulledLinearKoszulForms_homogeneous f V L hL w) k).ExactAt p
  exact nativeProjectiveKoszul_global_exactAt_of_chart (homogeneousQuotientPiece V.ideal.toIdeal)
    (fun j : Fin (n+1) => Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X j))
    (fun j => ⟨MvPolynomial.X j,MvPolynomial.isHomogeneous_X ℂ j,rfl⟩)
    (homogeneousQuotient_coordinate_adjoin_eq_top_unlifted V.ideal.toIdeal)
    (projectivePulledLinearKoszulForms f V L w)
    (projectivePulledLinearKoszulForms_homogeneous f V L hL w) k
    (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩
    (hcover w hwb) p hp (he w hwa k p hp)

end LinearStudy