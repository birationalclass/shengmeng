module
public import Linear.ProjectivePulledGlobalCokernelWholeCutNativeTwist
public import Linear.ProjectivePulledKoszulGlobalCokernelAugmentation
public import Linear.ChainActualCokernelTargetAugmentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading projectivePulledLinearKoszulComplex
  projectivePulledLinearKoszulForms nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm
  nativeProjectiveModuleSheaf originalChainCokernelTargetAugmentation
variable {n r : ℕ}

/-- In the ALREADY VERIFIED NONZERO defining-ideal branch,retain its
EXPLICIT hproper and ring-dimension hypotheses. Derive NONEMPTY open
BEFORE ALL integer k,a real quotient-induced augmentation to SAME WHOLE
original cut native twist along SAME closed embedding,and its quasiiso.
The exact zero-component formula is proved. Agreement with separately
defined canonical geometric quotient augmentation/epsilon is NOT claimed. -/
theorem projectivePulledLinearSection_exists_wholeCutNativeTwist_quotientAugmentation_quasiIso
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
        let J := projectivePulledLinearSectionIdeal f V L w
        let hJ := projectivePulledLinearSectionIdeal_isHomogeneous f V L hL w
        letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
        letI := homogeneousQuotientGrading J hJ
        ∀ k : ℤ,
          let C := projectivePulledLinearKoszulComplex f V L hL w k
          let T := (Scheme.Modules.pushforward (projectivePulledLinearSectionClosedEmbedding f V L hL w)).obj
            (nativeProjectiveModuleSheaf (homogeneousQuotientPiece J)
              (nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece J))
              (nativeProjectiveRingIntegerPiece_graded (homogeneousQuotientPiece J)) k)
          ∃ e : cokernel (C.d 1 0) ≅ T,
            QuasiIso (originalChainCokernelTargetAugmentation C T e) ∧
              (originalChainCokernelTargetAugmentation C T e).f 0 = cokernel.π (C.d 1 0) ≫ e.hom := by
  obtain ⟨cI,hcI,_,hgoodI⟩ := projectivePulledLinearSection_exists_globalCokernelWholeCutNativeTwistIso
    f V hq hf hV L hL hinj hfinite x0 hx0
  obtain ⟨cA,hcA,_,hgoodA⟩ := projectivePulledLinearSection_exists_globalCokernelAugmentation_quasiIso
    f V hproper hq hf hV L hL hinj hfinite hdim x0 hx0
  have hc : cI*cA ≠ 0 := mul_ne_zero hcI hcA
  have hex : ∃ w : Fin (r+1) → ℂ,MvPolynomial.eval w (cI*cA) ≠ 0 := by
    by_contra h
    push Not at h
    apply hc
    apply MvPolynomial.funext
    intro w
    rw [map_zero]
    exact h w
  refine ⟨cI*cA,hc,hex,?_⟩
  intro w hw
  rw [map_mul] at hw
  obtain ⟨hwI,hwA⟩ := mul_ne_zero_iff.mp hw
  let J := projectivePulledLinearSectionIdeal f V L w
  let hJ := projectivePulledLinearSectionIdeal_isHomogeneous f V L hL w
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI := homogeneousQuotientGrading J hJ
  dsimp only
  intro k
  obtain ⟨e⟩ := hgoodI w hwI k
  refine ⟨e,?_,originalChainCokernelTargetAugmentation_f_zero _ _ e⟩
  exact originalChainCokernelTargetAugmentation_quasiIso_of_cokernel _ _ e (hgoodA w hwA k)

end LinearStudy