module
public import Linear.FormalInverseJacobian
public import Linear.PowerSeriesCoordinateChart
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K α β : Type*} [Field K] [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β] [Nonempty β]

def smoothCoordinateImages (G : β → MvPowerSeries (α ⊕ β) K) :
    α ⊕ β → MvPowerSeries (α ⊕ β) K :=
  Sum.elim (fun i => MvPowerSeries.X (Sum.inl i)) G

omit [Nonempty β] in
theorem smoothCoordinateImages_linearPart_det
    (G : β → MvPowerSeries (α ⊕ β) K) :
    Matrix.det (fun i j =>
      (MvPowerSeries.pderiv j (smoothCoordinateImages G i)).constantCoeff) =
    Matrix.det (fun i j => (MvPowerSeries.pderiv (Sum.inr j) (G i)).constantCoeff) := by
  let C : Matrix β α K := fun i j => (MvPowerSeries.pderiv (Sum.inl j) (G i)).constantCoeff
  let D : Matrix β β K := fun i j => (MvPowerSeries.pderiv (Sum.inr j) (G i)).constantCoeff
  have he : (fun i j =>
      (MvPowerSeries.pderiv j (smoothCoordinateImages G i)).constantCoeff) =
      Matrix.fromBlocks (1 : Matrix α α K) 0 C D := by
    funext i j
    cases i <;> cases j <;>
      simp [smoothCoordinateImages, Matrix.fromBlocks, Matrix.one_apply,
        MvPowerSeries.pderiv_X, Pi.single_apply, C, D]
  rw [he, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Nonempty β] in
theorem smoothCoordinateImages_constantCoeff_zero
    (G : β → MvPowerSeries (α ⊕ β) K) (hG : ∀ j, (G j).constantCoeff = 0)
    (i : α ⊕ β) : (smoothCoordinateImages G i).constantCoeff = 0 := by
  cases i <;> simp [smoothCoordinateImages, hG]

def smoothFormalCoordinateEquiv
    (G : β → MvPowerSeries (α ⊕ β) K) (hG : ∀ j, (G j).constantCoeff = 0)
    (hJ : IsUnit (Matrix.det (fun i j =>
      (MvPowerSeries.pderiv (Sum.inr j) (G i)).constantCoeff))) :
    MvPowerSeries (α ⊕ β) K ≃ₐ[K] MvPowerSeries (α ⊕ β) K :=
  formalCoordinateEquivOfJacobianUnit (smoothCoordinateImages G)
    (smoothCoordinateImages_constantCoeff_zero G hG)
    (by rw [smoothCoordinateImages_linearPart_det]; exact hJ)

theorem smoothFormalCoordinateEquiv_parameter
    (G : β → MvPowerSeries (α ⊕ β) K) (hG : ∀ j, (G j).constantCoeff = 0)
    (hJ : IsUnit (Matrix.det (fun i j =>
      (MvPowerSeries.pderiv (Sum.inr j) (G i)).constantCoeff))) (i : α) :
    smoothFormalCoordinateEquiv G hG hJ (MvPowerSeries.X (Sum.inl i)) =
      MvPowerSeries.X (Sum.inl i) :=
  formalCoordinateEquivOfJacobianUnit_X _ _ _ _

theorem smoothFormalCoordinateEquiv_normal
    (G : β → MvPowerSeries (α ⊕ β) K) (hG : ∀ j, (G j).constantCoeff = 0)
    (hJ : IsUnit (Matrix.det (fun i j =>
      (MvPowerSeries.pderiv (Sum.inr j) (G i)).constantCoeff))) (j : β) :
    smoothFormalCoordinateEquiv G hG hJ (MvPowerSeries.X (Sum.inr j)) = G j :=
  formalCoordinateEquivOfJacobianUnit_X _ _ _ _

theorem smoothFormalCoordinateEquiv_parameter_series
    (G : β → MvPowerSeries (α ⊕ β) K) (hG : ∀ j, (G j).constantCoeff = 0)
    (hJ : IsUnit (Matrix.det (fun i j =>
      (MvPowerSeries.pderiv (Sum.inr j) (G i)).constantCoeff)))
    (b : MvPowerSeries α K) :
    smoothFormalCoordinateEquiv G hG hJ (MvPowerSeries.rename Sum.inl b) =
      MvPowerSeries.rename Sum.inl b := by
  let T := smoothCoordinateImages G
  have hT : Ideal.span (Set.range T) =
      IsLocalRing.maximalIdeal (MvPowerSeries (α ⊕ β) K) :=
    powerSeries_parameter_span_of_jacobian_unit T
      (smoothCoordinateImages_constantCoeff_zero G hG)
      (by rw [smoothCoordinateImages_linearPart_det]; exact hJ)
  change MvPowerSeries.substAlgHom (parameter_substitution_hasSubst T hT)
    (MvPowerSeries.rename Sum.inl b) = _
  rw [MvPowerSeries.substAlgHom_apply]
  rw [MvPowerSeries.rename_eq_subst, MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.HasSubst.X_comp Sum.inl) (parameter_substitution_hasSubst T hT)]
  congr 1
  funext i
  exact MvPowerSeries.subst_X (parameter_substitution_hasSubst T hT) (Sum.inl i)

end LinearStudy
