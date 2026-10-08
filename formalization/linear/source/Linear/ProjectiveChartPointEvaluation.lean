module
public import Linear.ProjectiveGoodAffineCoordinates
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {n : ℕ}

/-- Evaluation on the actual affine coordinate quotient at a specified
normalized point of the original V. -/
def IntegralProjectiveEquations.affinePointEvaluation
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ V.affineIdeal (MvPolynomial.aeval x)
    (fun p hp => RingHom.mem_ker.mp (V.affineIdeal_le_pointKernel x hx hp))

theorem IntegralProjectiveEquations.affinePointEvaluation_mk
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) (p : MvPolynomial (Fin n) ℂ) :
    V.affinePointEvaluation x hx (Ideal.Quotient.mk V.affineIdeal p) =
      MvPolynomial.eval x p := by
  exact Ideal.Quotient.lift_mk _ _ _

/-- Actual evaluation of the denominator-open quotient at the same source point. -/
def projectiveChartPointEvaluation
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (x : Fin n → ℂ) (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (hp0 : MvPolynomial.eval x (affineChartPolynomialMap (f.forms 0)) ≠ 0) :
    Localization.Away (projectiveChartDenominator f V) →ₐ[ℂ] ℂ :=
  IsLocalization.Away.liftAlgHom (projectiveChartDenominator f V)
    (f := V.affinePointEvaluation x hx)
    (isUnit_iff_ne_zero.mpr (by
      simpa only [projectiveChartDenominator, V.affinePointEvaluation_mk] using hp0))

theorem projectiveChartPointEvaluation_algebraMap
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (x : Fin n → ℂ) (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (hp0 : MvPolynomial.eval x (affineChartPolynomialMap (f.forms 0)) ≠ 0)
    (b : MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) :
    projectiveChartPointEvaluation f V x hx hp0
      (algebraMap _ (Localization.Away (projectiveChartDenominator f V)) b) =
      V.affinePointEvaluation x hx b := by
  simp [projectiveChartPointEvaluation]

theorem projectiveChartPointEvaluation_source_coordinates
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (x : Fin n → ℂ) (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (hp0 : MvPolynomial.eval x (affineChartPolynomialMap (f.forms 0)) ≠ 0) :
    ((projectiveChartPointEvaluation f V x hx hp0).comp
      (IsScalarTower.toAlgHom ℂ (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
        (Localization.Away (projectiveChartDenominator f V)))).comp
      (Ideal.Quotient.mkₐ ℂ V.affineIdeal) = MvPolynomial.aeval x := by
  apply MvPolynomial.algHom_ext
  intro i
  exact projectiveChartPointEvaluation_algebraMap f V x hx hp0 _ |>.trans
    (V.affinePointEvaluation_mk x hx _)

end LinearStudy
