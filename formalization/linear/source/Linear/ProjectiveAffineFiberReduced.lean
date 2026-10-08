module
public import Linear.ProjectiveAffineFiberMap
public import Linear.UnramifiedEvaluationQuotient
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {n : ℕ}

/-- Reducedness of the ACTUAL affine scheme fiber of the original projective
map, on its constructed target unramified open. -/
theorem projectiveAffineFiberQuotient_isReduced_of_target_open
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (y : Fin n → ℂ)
    (hy : normalizedProjectivePoint y ∈ V.zeroSet)
    (b : MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
    (hb : V.affinePointEvaluation y hy b ≠ 0)
    (hgood : let φ := projectiveChartOpenMap f V hq hf hV y hy
      letI : Algebra (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
        (Localization.Away (projectiveChartDenominator f V)) := φ.toRingHom.toAlgebra
      ↑(PrimeSpectrum.basicOpen (φ b)) ⊆
        Algebra.unramifiedLocus (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
          (Localization.Away (projectiveChartDenominator f V))) :
    IsReduced (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal f V y) := by
  let φ := projectiveChartOpenMap f V hq hf hV y hy
  let ρ := V.affinePointEvaluation y hy
  let ψ := projectiveAffineFiberChartMap f V y
  have hc : ψ.toRingHom.comp φ.toRingHom = (algebraMap ℂ _).comp ρ.toRingHom := by
    exact congrArg AlgHom.toRingHom (projectiveAffineFiberChartMap_pullback f V hq hf hV y hy)
  exact isReduced_of_unramified_evaluation_quotient φ.toRingHom ρ.toRingHom ψ.toRingHom b
    (projectiveAffineFiberChartMap_surjective f V y) hc hb hgood

end LinearStudy
