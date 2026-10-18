module
public import Linear.ProjectiveConeChartOpenIntersection
public import Linear.ProjectiveConeChartEvaluation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- Intersect a target cone nonvanishing set with the actual affine chart
open at one point. No projective representative normalization is assumed. -/
theorem projectiveCone_exists_target_chart_open_point
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (H : CoordinateRing n) (hH : H ∉ V.ideal.toIdeal)
    (p : MvPolynomial (Fin n) ℂ) (hp : p ∉ V.affineIdeal) :
    ∃ w : CoordinateVector n, w ∈ MvPolynomial.zeroLocus ℂ V.ideal.toIdeal ∧
      w 0 ≠ 0 ∧ MvPolynomial.eval w H ≠ 0 ∧
      MvPolynomial.eval (fun i => w i.succ / w 0) p ≠ 0 := by
  have hX : (MvPolynomial.X (0 : Fin (n + 1)) : CoordinateRing n) ∉
      V.ideal.toIdeal := by
    intro h
    have he := ((V.normalizedPoint_mem_iff x).mp hx) _ h
    simpa using he
  obtain ⟨P, k, hP, he⟩ := projectiveChartPolynomial_exists_cone_numerator V p hp
  have hprod : MvPolynomial.X 0 * H * P ∉ V.ideal.toIdeal := by
    intro h
    rcases V.prime.mem_or_mem h with hXH | hP'
    · rcases V.prime.mem_or_mem hXH with hX' | hH'
      · exact hX hX'
      · exact hH hH'
    · exact hP hP'
  obtain ⟨w, hwV, hwprod⟩ := projectiveCone_exists_nonvanishing_point V _ hprod
  have hm : w 0 * MvPolynomial.eval w H * MvPolynomial.eval w P ≠ 0 := by
    simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hwprod
  have hwp := (mul_ne_zero_iff.mp hm).2
  have hwh := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hm).1).2
  have hw0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hm).1).1
  refine ⟨w, hwV, hw0, hwh, ?_⟩
  intro hzero
  apply hwp
  rw [projectiveConeChart_numerator_eval w hw0 p P k he, hzero, zero_mul]

end LinearStudy
