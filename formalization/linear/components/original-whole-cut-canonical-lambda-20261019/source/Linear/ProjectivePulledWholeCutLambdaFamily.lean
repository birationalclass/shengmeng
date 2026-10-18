module
public import Linear.ProjectivePulledWholeCutArtinian
public import Linear.ProjectivePulledWholeCutResolutionObjects
public import Linear.SchemeModuleClosedDiscreteGlobalToInternalExtSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading nativeProjectiveModuleSheaf
variable {n r : ℕ}
/-- The ORIGINAL geometric hypotheses derive ONE NONEMPTY parameter open BEFORE ALL integer twists, ALL actual coefficients and ALL positive Ext degrees. On it the SAME canonical lambda for the WHOLE ORIGINAL cut's native resolution target is bijective. Artinian support and closed immersion are DERIVED,not assumed. -/
theorem projectivePulledLinearSection_exists_wholeCutCanonicalLambda_bijective
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
        ∀ k : ℤ, ∀ N : (Proj (homogeneousQuotientPiece V.ideal.toIdeal)).Modules, ∀ j : ℕ,
          Function.Bijective (schemeModuleGlobalToInternalExtSections
            (projectivePulledWholeCutResolutionTarget f V L hL w k) N j) := by
  obtain ⟨c,hc,hex,hgood⟩ := projectivePulledLinearSection_exists_wholeCut_isArtinian
    f V hq hf hV L hL hinj hfinite x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI : IsArtinianScheme (projectivePulledLinearSectionScheme f V L hL w) := hgood w hw
  letI : IsClosedImmersion (projectivePulledLinearSectionClosedEmbedding f V L hL w) :=
    projectivePulledLinearSectionClosedEmbedding_isClosedImmersion f V L hL w
  intro k N j
  unfold projectivePulledWholeCutResolutionTarget
  exact schemeModuleGlobalToInternalExtSections_artinianClosedImmersion_bijective
    (projectivePulledLinearSectionClosedEmbedding f V L hL w) _ N j
end LinearStudy
