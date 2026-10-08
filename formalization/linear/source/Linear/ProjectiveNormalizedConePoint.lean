module
public import Linear.ProjectiveAffineVariety
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

theorem normalizedProjectivePoint_coordinate_ratios
    (w : CoordinateVector n) (hw : w ≠ 0) (hw0 : w 0 ≠ 0) :
    normalizedProjectivePoint (fun i : Fin n => w i.succ / w 0) =
      Projectivization.mk ℂ w hw := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨(w 0)⁻¹, ?_⟩
  funext i
  cases i using Fin.cases with
  | zero => simp [Pi.smul_apply, smul_eq_mul, hw0]
  | succ i => simp [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem IntegralProjectiveEquations.normalizedConePoint_mem
    (V : IntegralProjectiveEquations n) (w : CoordinateVector n)
    (hwV : w ∈ MvPolynomial.zeroLocus ℂ V.ideal.toIdeal) (hw0 : w 0 ≠ 0) :
    normalizedProjectivePoint (fun i : Fin n => w i.succ / w 0) ∈ V.zeroSet := by
  have hw : w ≠ 0 := by
    intro h
    exact hw0 (congrFun h 0)
  rw [normalizedProjectivePoint_coordinate_ratios w hw hw0]
  exact (V.mem_zeroSet_mk w hw).mpr hwV

end LinearStudy
