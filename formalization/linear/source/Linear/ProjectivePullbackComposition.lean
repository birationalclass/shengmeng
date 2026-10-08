module
public import Linear.ProjectiveGenericFieldDegree
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- Pullback of the ORIGINAL coordinate-domain map reverses composition. -/
theorem projectiveCoordinateDomainMap_comp
    (f g : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hfq : 0 < f.degree) (hgq : 0 < g.degree)
    (hf : Function.Surjective f.onPoints) (hg : Function.Surjective g.onPoints)
    (hVf : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (hVg : g.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (hcq : 0 < (f.comp g).degree)
    (hc : Function.Surjective (f.comp g).onPoints)
    (hVc : (f.comp g).onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    projectiveCoordinateDomainMap (f.comp g) V hcq hc hVc =
      (projectiveCoordinateDomainMap g V hgq hg hVg).comp
        (projectiveCoordinateDomainMap f V hfq hf hVf) := by
  have hpoly : (MvPolynomial.aeval (f.comp g).forms : CoordinateRing n →ₐ[ℂ] CoordinateRing n) =
      (MvPolynomial.aeval g.forms).comp (MvPolynomial.aeval f.forms) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [MvPolynomial.aeval_X, AlgHom.comp_apply]
    rfl
  apply AlgHom.ext
  intro a
  obtain ⟨H, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [projectiveCoordinateDomainMap_mk, AlgHom.comp_apply,
    projectiveCoordinateDomainMap_mk, projectiveCoordinateDomainMap_mk]
  exact congrArg (Ideal.Quotient.mk V.ideal.toIdeal) (AlgHom.congr_fun hpoly H)

theorem projectiveCoordinateFractionMap_comp
    (f g : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hfq : 0 < f.degree) (hgq : 0 < g.degree)
    (hf : Function.Surjective f.onPoints) (hg : Function.Surjective g.onPoints)
    (hVf : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (hVg : g.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (hcq : 0 < (f.comp g).degree)
    (hc : Function.Surjective (f.comp g).onPoints)
    (hVc : (f.comp g).onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    letI := V.prime
    projectiveCoordinateFractionMap (f.comp g) V hcq hc hVc =
      (projectiveCoordinateFractionMap g V hgq hg hVg).comp
        (projectiveCoordinateFractionMap f V hfq hf hVf) := by
  letI := V.prime
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (nonZeroDivisors (CoordinateRing n ⧸ V.ideal.toIdeal))
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    AlgHom.comp_apply, projectiveCoordinateFractionMap_algebraMap]
  rw [projectiveCoordinateDomainMap_comp f g V hfq hgq hf hg hVf hVg hcq hc hVc]
  rfl

/-- The ORIGINAL projective function-field pullbacks are compatible
with composition through the SAME chart embedding. -/
theorem projectiveChartFractionMap_comp
    (f g : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hfq : 0 < f.degree) (hgq : 0 < g.degree)
    (hf : Function.Surjective f.onPoints) (hg : Function.Surjective g.onPoints)
    (hVf : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (hVg : g.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (hcq : 0 < (f.comp g).degree)
    (hc : Function.Surjective (f.comp g).onPoints)
    (hVc : (f.comp g).onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    letI := V.prime
    letI := V.affineIdeal_isPrime_of_point x0 hx0
    projectiveChartFractionMap (f.comp g) V hcq hc hVc x0 hx0 =
      (projectiveChartFractionMap g V hgq hg hVg x0 hx0).comp
        (projectiveChartFractionMap f V hfq hf hVf x0 hx0) := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x0 hx0
  apply AlgHom.ext
  intro z
  apply (projectiveChartFractionEmbedding V x0 hx0).injective
  change projectiveChartFractionEmbedding V x0 hx0
      (projectiveChartFractionMap (f.comp g) V hcq hc hVc x0 hx0 z) =
    projectiveChartFractionEmbedding V x0 hx0
      (projectiveChartFractionMap g V hgq hg hVg x0 hx0
        (projectiveChartFractionMap f V hfq hf hVf x0 hx0 z))
  rw [projectiveChartFractionMap_commutes,
    projectiveChartFractionMap_commutes, projectiveChartFractionMap_commutes,
    projectiveCoordinateFractionMap_comp f g V hfq hgq hf hg hVf hVg hcq hc hVc]
  rfl

end LinearStudy
