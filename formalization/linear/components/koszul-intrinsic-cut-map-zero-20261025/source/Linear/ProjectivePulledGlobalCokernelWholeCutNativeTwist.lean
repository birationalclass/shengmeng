module
public import Linear.ProjectivePulledGlobalCokernelWholeCutPushforward
public import Linear.NativeIntegerTwistWholeChartFrame
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading projectivePulledLinearKoszulForms
  nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm nativeProjectiveModuleSheaf
  nativeIntegerTwistWholeSheafIsoOfBasicOpenTop
variable {n r : ℕ}

/-- ORIGINAL hypotheses derive one NONEMPTY open BEFORE ALL integer k.
On it,the SAME NAMED original global Koszul actual d1-cokernel is the
WHOLE ORIGINAL cut's NATIVE degree-k associated sheaf,pushed along SAME
ACTUAL original homogeneous quotient closed embedding. Original chart
maps,embedding square and original X0-power frames are constructed.
This is an OBJECT isomorphism;original geometric augmentation/epsilon,
ambient pullback-twist compatibility and derived SHEAFExt remain separate. -/
theorem projectivePulledLinearSection_exists_globalCokernelWholeCutNativeTwistIso
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
        let J := projectivePulledLinearSectionIdeal f V L w
        let hJ := projectivePulledLinearSectionIdeal_isHomogeneous f V L hL w
        letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
        letI := homogeneousQuotientGrading J hJ
        ∀ k : ℤ,Nonempty (cokernel ((projectivePulledLinearKoszulComplex f V L hL w k).d 1 0) ≅
          (Scheme.Modules.pushforward (projectivePulledLinearSectionClosedEmbedding f V L hL w)).obj
            (nativeProjectiveModuleSheaf (homogeneousQuotientPiece J)
              (nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece J))
              (nativeProjectiveRingIntegerPiece_graded (homogeneousQuotientPiece J)) k)) := by
  obtain ⟨cM,hcM,_,hgoodM⟩ := projectivePulledLinearSection_exists_globalCokernelWholeCutPushforwardIso
    f V hq hf hV L hL hinj hfinite x0 hx0
  obtain ⟨cT,hcT,_,hgoodT⟩ := projectivePulledLinearSection_exists_native_open_coverage
    f V hq hf hV L hL hinj hfinite x0 hx0
  have hc : cM*cT ≠ 0 := mul_ne_zero hcM hcT
  have hex : ∃ w : Fin (r+1) → ℂ,MvPolynomial.eval w (cM*cT) ≠ 0 := by
    by_contra h
    push Not at h
    apply hc
    apply MvPolynomial.funext
    intro w
    rw [map_zero]
    exact h w
  refine ⟨cM*cT,hc,hex,?_⟩
  intro w hw
  rw [map_mul] at hw
  obtain ⟨hwM,hwT⟩ := mul_ne_zero_iff.mp hw
  let J := projectivePulledLinearSectionIdeal f V L w
  let hJ := projectivePulledLinearSectionIdeal_isHomogeneous f V L hL w
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI := homogeneousQuotientGrading J hJ
  dsimp only
  intro k
  obtain ⟨eM⟩ := hgoodM w hwM k
  let eT := nativeIntegerTwistWholeSheafIsoOfBasicOpenTop (homogeneousQuotientPiece J)
    (Ideal.Quotient.mk J (MvPolynomial.X 0))
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩ (hgoodT w hwT).1 k
  exact ⟨eM ≪≫ (Scheme.Modules.pushforward
    (projectivePulledLinearSectionClosedEmbedding f V L hL w)).mapIso eT⟩

end LinearStudy