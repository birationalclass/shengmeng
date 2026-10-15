module
public import Linear.ProjectivePulledPresentationProjectionCore
public import Linear.ProjectivePulledSectionNativeCoverage
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading projectivePulledLinearKoszulForms
  nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm nativeProjectiveKoszulMappedPresentationData
  CategoryTheory.Functor.mapHomologicalComplex
variable {n r : ℕ}

/-- These are the actual ambient cover and WHOLE-cut original X0-chart
coverage. This is a statement only. The following theorem derives both
on ONE nonempty parameter open from the original geometric hypotheses. -/
def projectivePulledWholeCutNativeAugmentationConditions
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) : Prop :=
  projectivePulledLinearKoszulAmbientCover f V L w ∧
    let J := projectivePulledLinearSectionIdeal f V L w
    letI := homogeneousQuotientGrading J (projectivePulledLinearSectionIdeal_isHomogeneous f V L hL w)
    Proj.basicOpen (homogeneousQuotientPiece J) (Ideal.Quotient.mk J (MvPolynomial.X 0)) = ⊤

/-- ORIGINAL hypotheses derive the two actual covers BEFORE ALL integer
indices. No projection formula,target iso or exactness is assumed. -/
theorem projectivePulledLinearSection_exists_wholeCutNativeAugmentationConditions
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
        projectivePulledWholeCutNativeAugmentationConditions f V L hL w := by
  obtain ⟨cM,hcM,_,hgoodM⟩ := projectivePulledLinearSection_exists_presentationAmbientCover
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
  exact ⟨hgoodM w hwM,(hgoodT w hwT).1⟩

end LinearStudy
