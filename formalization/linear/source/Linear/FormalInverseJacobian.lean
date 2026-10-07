module
public import Linear.ParameterSubstitution
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
theorem powerSeries_coefficient_matrix_linearPart
    (T : ι → MvPowerSeries ι K)
    (M : Matrix ι ι (MvPowerSeries ι K)) (hM : M.mulVec MvPowerSeries.X = T) :
    (fun i j => (M i j).constantCoeff) =
      (fun i j => (MvPowerSeries.pderiv j (T i)).constantCoeff) := by
  funext i j
  have h := congrArg (fun f : MvPowerSeries ι K =>
    (MvPowerSeries.pderiv j f).constantCoeff) (congrFun hM i)
  simpa [Matrix.mulVec, dotProduct, map_sum, Derivation.leibniz,
    smul_eq_mul, MvPowerSeries.pderiv_X, Pi.single_apply, mul_ite, apply_ite] using h

theorem powerSeries_parameter_span_of_jacobian_unit
    (T : ι → MvPowerSeries ι K) (h0 : ∀ i, (T i).constantCoeff = 0)
    (hJ : IsUnit (Matrix.det (fun i j =>
      (MvPowerSeries.pderiv j (T i)).constantCoeff))) :
    Ideal.span (Set.range T) = IsLocalRing.maximalIdeal (MvPowerSeries ι K) := by
  obtain ⟨M, hM⟩ := powerSeries_equation_coefficient_matrix T h0
  have hd : IsUnit M.det := by
    apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
    rw [RingHom.map_det]
    change IsUnit (Matrix.det (fun i j => (M i j).constantCoeff))
    rw [powerSeries_coefficient_matrix_linearPart T M hM]
    exact hJ
  have he : M⁻¹.mulVec T = MvPowerSeries.X := by
    rw [← hM, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change ¬ IsUnit (T i)
    simp [MvPowerSeries.isUnit_iff_constantCoeff, h0 i]
  · rw [← powerSeries_coordinateIdeal_eq_maximalIdeal]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [← congrFun he i]
    apply Submodule.sum_mem
    intro j hj
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_range_self)

def formalCoordinateEquivOfJacobianUnit
    (T : ι → MvPowerSeries ι K) (h0 : ∀ i, (T i).constantCoeff = 0)
    (hJ : IsUnit (Matrix.det (fun i j =>
      (MvPowerSeries.pderiv j (T i)).constantCoeff))) :
    MvPowerSeries ι K ≃ₐ[K] MvPowerSeries ι K :=
  parameterSubstitutionEquiv T (powerSeries_parameter_span_of_jacobian_unit T h0 hJ)

theorem formalCoordinateEquivOfJacobianUnit_X
    (T : ι → MvPowerSeries ι K) (h0 : ∀ i, (T i).constantCoeff = 0)
    (hJ : IsUnit (Matrix.det (fun i j =>
      (MvPowerSeries.pderiv j (T i)).constantCoeff))) (i : ι) :
    formalCoordinateEquivOfJacobianUnit T h0 hJ (MvPowerSeries.X i) = T i :=
  parameterSubstitutionEquiv_X T _ i

end LinearStudy
