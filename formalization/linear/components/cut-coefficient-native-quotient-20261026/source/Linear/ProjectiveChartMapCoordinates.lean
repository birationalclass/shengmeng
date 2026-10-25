module
public import Linear.ProjectiveChartGenericMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

theorem projectiveChartFractionEmbedding_algebraMap
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (P : MvPolynomial (Fin n) ℂ) :
    letI := V.prime
    letI := V.affineIdeal_isPrime_of_point x hx
    projectiveChartFractionEmbedding V x hx
      (algebraMap _ (FractionRing _) (Ideal.Quotient.mk V.affineIdeal P)) =
      coordinateRatioPolynomialMap (projectiveConeFractionCoordinates V) P := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  change IsFractionRing.lift (projectiveChartCoordinateEmbedding_injective V x hx)
      (algebraMap _ (FractionRing _) (Ideal.Quotient.mk V.affineIdeal P)) = _
  rw [IsFractionRing.lift_algebraMap]
  exact projectiveChartCoordinateEmbedding_mk V x hx P

/-- The actual conjugate field map agrees with the rational f_i/f_0 coordinate pullback. -/
theorem projectiveChartFractionMap_coordinate
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) (i : Fin n) :
    letI := V.prime
    letI := V.affineIdeal_isPrime_of_point x hx
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let L := FractionRing B
    projectiveChartFractionMap f V hq hf hV x hx
      (algebraMap B L (Ideal.Quotient.mk V.affineIdeal (MvPolynomial.X i))) =
        algebraMap B L (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap (f.forms i.succ))) /
          algebraMap B L (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap (f.forms 0))) := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  intro B L
  apply (projectiveChartFractionEmbedding V x hx).injective
  change projectiveChartFractionEmbedding V x hx
      (projectiveChartFractionMap f V hq hf hV x hx
        (algebraMap B L (Ideal.Quotient.mk V.affineIdeal (MvPolynomial.X i)))) =
    projectiveChartFractionEmbedding V x hx
      (algebraMap B L (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap (f.forms i.succ))) /
        algebraMap B L (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap (f.forms 0))))
  rw [projectiveChartFractionMap_commutes, map_div₀,
    projectiveChartFractionEmbedding_algebraMap,
    projectiveChartFractionEmbedding_algebraMap,
    projectiveChartFractionEmbedding_algebraMap]
  change projectiveCoordinateFractionMap f V hq hf hV
      ((MvPolynomial.aeval (fun j : Fin n =>
        projectiveConeFractionCoordinates V j.succ / projectiveConeFractionCoordinates V 0))
        (MvPolynomial.X i)) = _
  rw [MvPolynomial.aeval_X, map_div₀,
    projectiveCoordinateFractionMap_coordinate, projectiveCoordinateFractionMap_coordinate]
  exact homogeneous_ratio_eq_chart_ratio _
    (projectiveConeFractionCoordinates_zero_ne_zero V x hx) _ _
    (f.homogeneous i.succ) (f.homogeneous 0)

/-- Projective surjectivity prevents the target chart denominator from vanishing identically. -/
theorem projectiveChart_denominator_ne_zero
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap (f.forms 0)) ≠ 0 := by
  letI := V.prime
  have hc := projectiveConeFractionCoordinates_zero_ne_zero V x hx
  have he : MvPolynomial.aeval (projectiveConeFractionCoordinates V) (f.forms 0) ≠ 0 := by
    rw [← projectiveCoordinateFractionMap_coordinate f V hq hf hV 0]
    intro hz
    apply hc
    exact (projectiveCoordinateFractionMap f V hq hf hV).injective (by simpa using hz)
  intro hz
  have hz' := congrArg (projectiveChartCoordinateEmbedding V x hx) hz
  rw [projectiveChartCoordinateEmbedding_mk, map_zero,
    coordinateRatioPolynomialMap_homogeneous _ hc _ (f.homogeneous 0)] at hz'
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hc)) he hz'

end LinearStudy
