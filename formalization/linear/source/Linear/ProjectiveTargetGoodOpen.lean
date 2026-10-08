module
public import Linear.FractionModelAlgebraicOpen
public import Linear.ProjectiveChartSmoothUnramified
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- Algebraicity is derived for the original rational chart map, with its
actual algebra action, from the finite original function-field map. -/
theorem projectiveChartOpenMap_isAlgebraic
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := V.affineIdeal_isPrime_of_point x hx
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let A := Localization.Away (projectiveChartDenominator f V)
    letI : Algebra B A := (projectiveChartOpenMap f V hq hf hV x hx).toAlgebra
    Algebra.IsAlgebraic B A := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let L := FractionRing B
  let φ := (projectiveChartOpenMap f V hq hf hV x hx).toRingHom
  let e := (awayFractionEmbedding (K := ℂ) (projectiveChartDenominator f V)
    (projectiveChart_denominator_ne_zero f V hq hf hV x hx)).toRingHom
  let χ := (projectiveChartFractionMap f V hq hf hV x hx).toRingHom
  have he : Function.Injective e := awayFractionEmbedding_injective
    (K := ℂ) (projectiveChartDenominator f V)
      (projectiveChart_denominator_ne_zero f V hq hf hV x hx)
  have hχ : χ.Finite := projectiveChartFractionMap_finite f V hq hf hV x hx
  have hcomp : e.comp φ = χ.comp (algebraMap B L) :=
    congrArg AlgHom.toRingHom (projectiveChartOpenMap_fraction_comp f V hq hf hV x hx)
  exact ringHom_finite_fraction_model_isAlgebraic φ e he χ hχ hcomp

/-- On a nonempty target basic open, EVERY preimage in the actual denominator
chart lies in the same smooth unramified source open. This is a chart-level
statement and does not claim coverage of points outside that source chart. -/
theorem projectiveChartOpenMap_exists_target_good_open
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    ∃ (b : MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
      (a : Localization.Away (projectiveChartDenominator f V)),
      b ≠ 0 ∧ a ≠ 0 ∧ Algebra.Smooth ℂ (Localization.Away a) ∧
      ((algebraMap (Localization.Away (projectiveChartDenominator f V))
          (Localization.Away a)).comp
        (projectiveChartOpenMap f V hq hf hV x hx).toRingHom).FormallyUnramified ∧
      ∀ P : PrimeSpectrum (Localization.Away (projectiveChartDenominator f V)),
        projectiveChartOpenMap f V hq hf hV x hx b ∉ P.asIdeal → a ∉ P.asIdeal := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let A := Localization.Away (projectiveChartDenominator f V)
  letI : IsDomain A := Localization.Away.isDomain
    (projectiveChart_denominator_ne_zero f V hq hf hV x hx)
  let φ := (projectiveChartOpenMap f V hq hf hV x hx).toRingHom
  obtain ⟨a, ha, hs, hu⟩ := projectiveChartOpenMap_exists_smooth_unramified_open
    f V hq hf hV x hx
  obtain ⟨b, hb, hab⟩ := ringHom_algebraic_target_open_avoids_source_closed
    φ (projectiveChartOpenMap_isAlgebraic f V hq hf hV x hx) a ha
  exact ⟨b, a, hb, ha, hs, hu, hab⟩

end LinearStudy
