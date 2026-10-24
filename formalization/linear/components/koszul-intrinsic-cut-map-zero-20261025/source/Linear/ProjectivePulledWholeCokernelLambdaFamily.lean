module
public import Linear.ProjectivePulledWholeCutArtinian
public import Linear.ProjectivePulledGlobalCokernelWholeCutNativeTwist
public import Linear.ProjectivePulledWholeCokernelLambdaStatement
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading projectivePulledLinearKoszulComplex
  nativeProjectiveModuleSheaf projectivePulledOriginalCokernelLambdaStatement
variable {n r : ℕ}
/-- ORIGINAL geometry derives canonical lambda bijectivity on the SAME actual original global Koszul d1-cokernel. ONE NONEMPTY parameter open is chosen BEFORE ALL integer k,arbitrary actual coefficients and positive Ext degrees. The source-to-whole-cut identification and Artinian support are DERIVED,not assumed. -/
theorem projectivePulledLinearSection_exists_originalCokernelCanonicalLambda_bijective
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ c : MvPolynomial (Fin (r+1)) ℂ, c ≠ 0 ∧
      (∃ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0) ∧
      ∀ w : Fin (r+1) → ℂ, MvPolynomial.eval w c ≠ 0 →
        letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
        ∀ k : ℤ, projectivePulledOriginalCokernelLambdaStatement f V L hL w k := by
  obtain ⟨cA,hcA,_,hgoodA⟩ := projectivePulledLinearSection_exists_wholeCut_isArtinian
    f V hq hf hV L hL hinj hfinite x0 hx0
  obtain ⟨cM,hcM,_,hgoodM⟩ := projectivePulledLinearSection_exists_globalCokernelWholeCutNativeTwistIso
    f V hq hf hV L hL hinj hfinite x0 hx0
  have hc : cA*cM ≠ 0 := mul_ne_zero hcA hcM
  have hex : ∃ w : Fin (r+1) → ℂ, MvPolynomial.eval w (cA*cM) ≠ 0 := by
    by_contra h
    push Not at h
    apply hc
    apply MvPolynomial.funext
    intro w
    rw [map_zero]
    exact h w
  refine ⟨cA*cM,hc,hex,?_⟩
  intro w hw
  rw [map_mul] at hw
  obtain ⟨hwA,hwM⟩ := mul_ne_zero_iff.mp hw
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI : IsArtinianScheme (projectivePulledLinearSectionScheme f V L hL w) := hgoodA w hwA
  letI : IsClosedImmersion (projectivePulledLinearSectionClosedEmbedding f V L hL w) :=
    projectivePulledLinearSectionClosedEmbedding_isClosedImmersion f V L hL w
  intro k
  obtain ⟨e⟩ := hgoodM w hwM k
  exact projectivePulledOriginalCokernelLambdaStatement_proof f V L hL w k
    (hgoodA w hwA) e
end LinearStudy
