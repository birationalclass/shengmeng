module
public import Linear.ProjectiveChartUnramifiedOpen
public import Linear.GenericSmoothUnramifiedOpen
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

theorem projectiveChartOpenMap_injective
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    Function.Injective (projectiveChartOpenMap f V hq hf hV x hx) := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let L := FractionRing B
  have hc : Function.Injective
      ((projectiveChartFractionMap f V hq hf hV x hx).comp (IsScalarTower.toAlgHom ℂ B L)) :=
    (projectiveChartFractionMap f V hq hf hV x hx).injective.comp (IsFractionRing.injective B L)
  rw [← projectiveChartOpenMap_fraction_comp f V hq hf hV x hx] at hc
  intro a b hab
  apply hc
  change awayFractionEmbedding (K := ℂ) (projectiveChartDenominator f V)
      (projectiveChart_denominator_ne_zero f V hq hf hV x hx)
        (projectiveChartOpenMap f V hq hf hV x hx a) =
    awayFractionEmbedding (K := ℂ) (projectiveChartDenominator f V)
      (projectiveChart_denominator_ne_zero f V hq hf hV x hx)
        (projectiveChartOpenMap f V hq hf hV x hx b)
  rw [hab]

/-- Simultaneous smoothness and nonramification for an actual nonempty source-chart open.
This does not yet assert smoothness at the image or whole-fiber containment. -/
theorem projectiveChartOpenMap_exists_smooth_unramified_open
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    ∃ b : Localization.Away (projectiveChartDenominator f V), b ≠ 0 ∧
      Algebra.Smooth ℂ (Localization.Away b) ∧
      ((algebraMap (Localization.Away (projectiveChartDenominator f V))
          (Localization.Away b)).comp
        (projectiveChartOpenMap f V hq hf hV x hx).toRingHom).FormallyUnramified := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let a := projectiveChartDenominator f V
  have ha : a ≠ 0 := projectiveChart_denominator_ne_zero f V hq hf hV x hx
  let A := Localization.Away a
  let L := FractionRing B
  letI : IsDomain A := Localization.Away.isDomain ha
  letI : Algebra.FinitePresentation ℂ A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  letI : Algebra A L := (awayFractionEmbedding (K := ℂ) a ha).toRingHom.toAlgebra
  letI : IsScalarTower B A L := IsScalarTower.of_algebraMap_eq
    (fun b => (awayFractionEmbedding_algebraMap (K := ℂ) a ha b).symm)
  letI : IsFractionRing A L := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers a) A L
  exact ringHom_fractionModel_exists_smooth_unramified_open (K := ℂ) (L := L)
    (projectiveChartOpenMap f V hq hf hV x hx).toRingHom
    (projectiveChartOpenMap_finiteType f V hq hf hV x hx).essFiniteType
    (projectiveChartOpenMap_fraction_comp_formallyUnramified f V hq hf hV x hx)

end LinearStudy
