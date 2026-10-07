module
public import Linear.ProjectiveAffineVariety
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

def IntegralProjectiveEquations.affinePointIdeal
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ) :
    Ideal (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) :=
  (RingHom.ker (MvPolynomial.aeval (R := ℂ) x).toRingHom).map
    (Ideal.Quotient.mk V.affineIdeal)

theorem IntegralProjectiveEquations.affinePointIdeal_isPrime
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    (V.affinePointIdeal x).IsPrime :=
  (affineChartPolynomialMap_point_quotient_prime V.ideal.toIdeal x
    ((V.normalizedPoint_mem_iff x).mp hx)).1

theorem IntegralProjectiveEquations.affinePointIdeal_comap
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    (V.affinePointIdeal x).comap (Ideal.Quotient.mk V.affineIdeal) =
      RingHom.ker (MvPolynomial.aeval (R := ℂ) x).toRingHom :=
  (affineChartPolynomialMap_point_quotient_prime V.ideal.toIdeal x
    ((V.normalizedPoint_mem_iff x).mp hx)).2

/-- The actual invariant projective point supplies the target quotient prime,
the point-local pullback compatibility and the ideal power sandwich. -/
theorem projective_total_invariance_actual_affine_point_data
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hf : f.degree ≠ 0) (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (x : Fin n → ℂ) (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (hp0 : MvPolynomial.eval x (affineChartPolynomialMap (f.forms 0)) ≠ 0) :
    let p0 := affineChartPolynomialMap (f.forms 0)
    let p := fun i : Fin n => affineChartPolynomialMap (f.forms i.succ)
    let y := fun i => MvPolynomial.eval x (p i) / MvPolynomial.eval x p0
    let P := RingHom.ker (polynomialAwayPointEvaluation x p0 hp0).toRingHom
    (V.affinePointIdeal y).IsPrime ∧
      (V.affinePointIdeal y).comap (Ideal.Quotient.mk V.affineIdeal) =
        P.comap (rationalPolynomialChartMap p0 p).toRingHom ∧
      ∃ e : ℕ, 0 < e ∧
        (V.affineIdeal.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.Away p0))) ^ e ≤
          V.affineIdeal.map (rationalPolynomialChartMap p0 p).toRingHom ∧
        V.affineIdeal.map (rationalPolynomialChartMap p0 p).toRingHom ≤
          V.affineIdeal.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.Away p0)) := by
  intro p0 p y P
  have hy := projective_total_invariance_affine_image_mem f V hV x hx hp0
  refine ⟨V.affinePointIdeal_isPrime y hy, ?_,
    projective_total_invariance_rational_chart_sandwich f V hf hV⟩
  rw [V.affinePointIdeal_comap y hy]
  exact rationalPolynomialChartMap_point_kernel x p0 hp0 p

end LinearStudy
