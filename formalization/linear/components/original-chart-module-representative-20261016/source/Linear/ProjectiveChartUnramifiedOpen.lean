module
public import Linear.ProjectiveChartOpenMap
public import Linear.AwayFractionUnramified
public import Mathlib.RingTheory.RingHom.FiniteType
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

theorem projectiveChartOpenMap_finiteType
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    (projectiveChartOpenMap f V hq hf hV x hx).toRingHom.FiniteType := by
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let A := Localization.Away (projectiveChartDenominator f V)
  let φ := projectiveChartOpenMap f V hq hf hV x hx
  have he : φ.toRingHom.comp (algebraMap ℂ B) = algebraMap ℂ A := by
    apply RingHom.ext
    intro c
    exact φ.commutes c
  have hc : (φ.toRingHom.comp (algebraMap ℂ B)).FiniteType := by
    rw [he, RingHom.finiteType_algebraMap]
    infer_instance
  exact RingHom.FiniteType.of_comp_finiteType hc

theorem projectiveChartOpenMap_fraction_comp_formallyUnramified
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    letI := V.affineIdeal_isPrime_of_point x hx
    ((awayFractionEmbedding (K := ℂ) (projectiveChartDenominator f V)
      (projectiveChart_denominator_ne_zero f V hq hf hV x hx)).toRingHom.comp
        (projectiveChartOpenMap f V hq hf hV x hx).toRingHom).FormallyUnramified := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let L := FractionRing B
  have hi : (algebraMap B L).FormallyUnramified :=
    RingHom.formallyUnramified_algebraMap.mpr
      (Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors B))
  have hc := hi.comp (projectiveChartFractionMap_formallyUnramified f V hq hf hV x hx)
  have he := congrArg AlgHom.toRingHom
    (projectiveChartOpenMap_fraction_comp f V hq hf hV x hx)
  change (awayFractionEmbedding (K := ℂ) (projectiveChartDenominator f V)
      (projectiveChart_denominator_ne_zero f V hq hf hV x hx)).toRingHom.comp
        (projectiveChartOpenMap f V hq hf hV x hx).toRingHom =
    (projectiveChartFractionMap f V hq hf hV x hx).toRingHom.comp (algebraMap B L) at he
  rw [he]
  exact hc

/-- A nonempty unramified open for the actual rational chart map.
This is still a source-chart open, not a whole-fiber or fiber-degree conclusion. -/
theorem projectiveChartOpenMap_exists_nonzero_unramified_open
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    ∃ b : Localization.Away (projectiveChartDenominator f V), b ≠ 0 ∧
      ((algebraMap (Localization.Away (projectiveChartDenominator f V))
          (Localization.Away b)).comp
        (projectiveChartOpenMap f V hq hf hV x hx).toRingHom).FormallyUnramified := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x hx
  exact awayFractionEmbedding_exists_unramified_open (K := ℂ)
    (projectiveChartDenominator f V) (projectiveChart_denominator_ne_zero f V hq hf hV x hx)
    (projectiveChartOpenMap f V hq hf hV x hx).toRingHom
    (projectiveChartOpenMap_finiteType f V hq hf hV x hx).essFiniteType
    (projectiveChartOpenMap_fraction_comp_formallyUnramified f V hq hf hV x hx)

end LinearStudy
