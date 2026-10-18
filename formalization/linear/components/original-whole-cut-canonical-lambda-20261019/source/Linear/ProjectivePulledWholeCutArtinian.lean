module
public import Linear.ProjectivePulledSectionGlobalReduced
public import Linear.FiniteCutArtinianTopology
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading
variable {n r : ℕ}
/-- ORIGINAL geometry derives actual Artinian structure on the WHOLE original cut on ONE NONEMPTY parameter open, independently of ALL twists and coefficient sheaves. No Artinian/discrete/support input is assumed. -/
theorem projectivePulledLinearSection_exists_wholeCut_isArtinian
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
        IsArtinianScheme (projectivePulledLinearSectionScheme f V L hL w) := by
  obtain ⟨c,hc,hex,hgood⟩ := projectivePulledLinearSection_exists_global_finite_reduced_schemes
    f V hq hf hV L hL hinj hfinite x0 hx0
  refine ⟨c,hc,hex,?_⟩
  intro w hw
  obtain ⟨_,_,hfin,⟨e⟩,_⟩ := hgood w hw
  let C := MvPolynomial (Fin n) ℂ ⧸
    (projectivePulledLinearSectionIdeal f V L w).map (affineChartPolynomialMap (K := ℂ)).toRingHom
  letI : Module.Finite ℂ C := hfin
  exact finiteFieldAlgebra_scheme_isArtinian_of_iso ℂ (CommRingCat.of C)
    (projectivePulledLinearSectionScheme f V L hL w) e
end LinearStudy
