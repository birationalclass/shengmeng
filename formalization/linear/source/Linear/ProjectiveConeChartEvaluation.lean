module
public import Linear.ProjectiveAffineVariety
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- Evaluation of the actual cone chart localization at a non-infinity point. -/
def projectiveConeChartEvaluation (w : CoordinateVector n) (hw : w 0 ≠ 0) :
    Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : CoordinateRing n) →ₐ[ℂ] ℂ :=
  IsLocalization.Away.liftAlgHom (MvPolynomial.X (0 : Fin (n + 1)) : CoordinateRing n)
    (f := MvPolynomial.aeval w) (by simpa using isUnit_iff_ne_zero.mpr hw)

theorem projectiveConeChartEvaluation_algebraMap
    (w : CoordinateVector n) (hw : w 0 ≠ 0) (H : CoordinateRing n) :
    projectiveConeChartEvaluation w hw
      (algebraMap (CoordinateRing n)
        (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : CoordinateRing n)) H) =
      MvPolynomial.eval w H := by
  simp [projectiveConeChartEvaluation]

theorem projectiveConeChartEvaluation_invSelf
    (w : CoordinateVector n) (hw : w 0 ≠ 0) :
    projectiveConeChartEvaluation w hw
      (IsLocalization.Away.invSelf (MvPolynomial.X (0 : Fin (n + 1)) : CoordinateRing n)) =
      (w 0)⁻¹ := by
  have h := congrArg (projectiveConeChartEvaluation w hw)
    (IsLocalization.Away.mul_invSelf
      (S := Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : CoordinateRing n))
      (MvPolynomial.X (0 : Fin (n + 1)) : CoordinateRing n))
  rw [map_mul, map_one, projectiveConeChartEvaluation_algebraMap,
    MvPolynomial.eval_X] at h
  apply (mul_left_cancel₀ hw)
  rw [mul_inv_cancel₀ hw]
  exact h

/-- Localized cone evaluation is exactly evaluation at the projective
coordinate ratios, rather than at an independently chosen affine point. -/
theorem projectiveConeChartEvaluation_chartPolynomial
    (w : CoordinateVector n) (hw : w 0 ≠ 0) (p : MvPolynomial (Fin n) ℂ) :
    projectiveConeChartEvaluation w hw (projectiveChartLocalizationMap p) =
      MvPolynomial.eval (fun i => w i.succ / w 0) p := by
  have he : (projectiveConeChartEvaluation w hw).comp projectiveChartLocalizationMap =
      MvPolynomial.aeval (fun i => w i.succ / w 0) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [projectiveChartLocalizationMap, projectiveConeChartEvaluation_algebraMap,
      projectiveConeChartEvaluation_invSelf, div_eq_mul_inv]
  exact congrArg (fun e : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ => e p) he

/-- Clearing denominators preserves a nonvanishing condition at the actual
normalized projective point. -/
theorem projectiveConeChart_numerator_eval
    (w : CoordinateVector n) (hw : w 0 ≠ 0) (p : MvPolynomial (Fin n) ℂ)
    (H : CoordinateRing n) (k : ℕ)
    (hH : algebraMap (CoordinateRing n)
      (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : CoordinateRing n)) H =
      projectiveChartLocalizationMap p *
        algebraMap (CoordinateRing n)
          (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) : CoordinateRing n))
            (MvPolynomial.X 0) ^ k) :
    MvPolynomial.eval w H =
      MvPolynomial.eval (fun i => w i.succ / w 0) p * (w 0) ^ k := by
  have he := congrArg (projectiveConeChartEvaluation w hw) hH
  simpa only [map_mul, map_pow, projectiveConeChartEvaluation_algebraMap,
    projectiveConeChartEvaluation_chartPolynomial, MvPolynomial.eval_X] using he

end LinearStudy
