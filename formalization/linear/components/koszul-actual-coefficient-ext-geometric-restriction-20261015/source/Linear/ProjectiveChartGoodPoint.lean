module
public import Linear.ProjectiveChartSmoothUnramified
public import Linear.GoodRationalPointForMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- An actual source-chart point which is smooth and unramified, with smooth image.
This is a single-point construction, not yet a statement about every point of a fiber. -/
theorem projectiveChartOpenMap_exists_good_rational_point
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let A := Localization.Away (projectiveChartDenominator f V)
    let φ := projectiveChartOpenMap f V hq hf hV x hx
    letI : Algebra B A := φ.toRingHom.toAlgebra
    ∃ ρ : A →ₐ[ℂ] ℂ,
      rationalPointPrime ρ ∈ Algebra.smoothLocus ℂ A ∧
      rationalPointPrime (ρ.comp φ) ∈ Algebra.smoothLocus ℂ B ∧
      rationalPointPrime ρ ∈ Algebra.unramifiedLocus B A := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let A := Localization.Away (projectiveChartDenominator f V)
  let φ := projectiveChartOpenMap f V hq hf hV x hx
  letI : IsDomain A := Localization.Away.isDomain
    (projectiveChart_denominator_ne_zero f V hq hf hV x hx)
  letI : Algebra.FinitePresentation ℂ B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  letI : Algebra.FinitePresentation ℂ A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨b, hb, hU⟩ := projectiveChartOpenMap_exists_nonzero_unramified_open f V hq hf hV x hx
  exact injectiveMap_exists_smooth_unramified_rational_point φ
    (projectiveChartOpenMap_injective f V hq hf hV x hx) b hb hU

end LinearStudy
