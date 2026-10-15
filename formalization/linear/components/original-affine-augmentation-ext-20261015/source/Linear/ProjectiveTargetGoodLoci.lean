module
public import Linear.TargetGoodLoci
public import Linear.ProjectiveTargetGoodOpen
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- Every prime preimage over one nonempty target open has smooth source,
smooth image and actual unramification, in the present denominator chart. -/
theorem projectiveChartOpenMap_exists_target_good_loci
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let A := Localization.Away (projectiveChartDenominator f V)
    let φ := projectiveChartOpenMap f V hq hf hV x hx
    letI : Algebra B A := φ.toRingHom.toAlgebra
    ∃ b : B, b ≠ 0 ∧ φ b ≠ 0 ∧ ∀ P : PrimeSpectrum A,
      φ b ∉ P.asIdeal → P ∈ Algebra.smoothLocus ℂ A ∧
        PrimeSpectrum.comap φ.toRingHom P ∈ Algebra.smoothLocus ℂ B ∧
        P ∈ Algebra.unramifiedLocus B A := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let A := Localization.Away (projectiveChartDenominator f V)
  letI : IsDomain A := Localization.Away.isDomain
    (projectiveChart_denominator_ne_zero f V hq hf hV x hx)
  letI : Algebra.FinitePresentation ℂ B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  letI : Algebra.FinitePresentation ℂ A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨a, ha, hs, hu⟩ := projectiveChartOpenMap_exists_smooth_unramified_open
    f V hq hf hV x hx
  exact injective_algebraic_map_exists_target_good_loci
    (projectiveChartOpenMap f V hq hf hV x hx)
    (projectiveChartOpenMap_injective f V hq hf hV x hx)
    (projectiveChartOpenMap_isAlgebraic f V hq hf hV x hx) a ha hs hu

end LinearStudy
