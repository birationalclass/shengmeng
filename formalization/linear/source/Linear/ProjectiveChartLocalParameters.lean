module
public import Linear.ProjectiveChartGoodPoint
public import Linear.RationalPointLocalMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- The actual projective chart map admits a smooth, unramified local pullback
which carries target maximal-ideal generators to source generators. The target
generators and the full fiber are not constructed by this statement. -/
theorem projectiveChartOpenMap_exists_good_local_parameters {ι : Type*}
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
      rationalPointPrime ρ ∈ Algebra.unramifiedLocus B A ∧
      ∀ (t : ι → Localization.AtPrime (rationalPointPrime (ρ.comp φ)).asIdeal),
        Ideal.span (Set.range t) = IsLocalRing.maximalIdeal
          (Localization.AtPrime (rationalPointPrime (ρ.comp φ)).asIdeal) →
        Ideal.span (Set.range (fun i => rationalPointLocalMap φ ρ (t i))) =
          IsLocalRing.maximalIdeal (Localization.AtPrime (rationalPointPrime ρ).asIdeal) := by
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let A := Localization.Away (projectiveChartDenominator f V)
  let φ := projectiveChartOpenMap f V hq hf hV x hx
  letI : Algebra B A := φ.toRingHom.toAlgebra
  obtain ⟨ρ, hsource, himage, hunram⟩ :=
    projectiveChartOpenMap_exists_good_rational_point f V hq hf hV x hx
  refine ⟨ρ, hsource, himage, hunram, ?_⟩
  intro t ht
  exact rationalPointLocalMap_parameters_generate φ ρ
    (projectiveChartOpenMap_finiteType f V hq hf hV x hx).essFiniteType hunram t ht

end LinearStudy
