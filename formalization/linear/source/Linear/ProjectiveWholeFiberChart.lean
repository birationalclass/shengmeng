module
public import Linear.ProjectiveFiberChartAvoidance
public import Linear.ProjectiveFibersFinite
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- The coordinate-domain divisibility identity forces each actual cone
preimage over the target nonvanishing set to avoid infinity. -/
theorem projectiveCone_chart_avoidance_eval
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (H C : CoordinateRing n)
    (hrel : (MvPolynomial.aeval f.forms) H - MvPolynomial.X 0 * C ∈ V.ideal.toIdeal)
    (v : CoordinateVector n) (hv : v ∈ MvPolynomial.zeroLocus ℂ V.ideal.toIdeal)
    (hH : MvPolynomial.eval (f.evalVector v) H ≠ 0) : v 0 ≠ 0 := by
  intro hv0
  have he := hv _ hrel
  change MvPolynomial.eval v ((MvPolynomial.aeval f.forms) H - MvPolynomial.X 0 * C) = 0 at he
  rw [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_X, hv0,
    zero_mul, sub_zero] at he
  exact hH ((MvPolynomial.eval_assoc f.forms v H).trans he)

/-- Normalize the entire projective fiber to the SAME target vector using
q-th roots. All its source points then lie in the standard source chart. -/
theorem projectiveWholeFiber_chart_avoidance
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (H C : CoordinateRing n)
    (hrel : (MvPolynomial.aeval f.forms) H - MvPolynomial.X 0 * C ∈ V.ideal.toIdeal)
    (w : CoordinateVector n) (hw : w ≠ 0)
    (hwV : w ∈ MvPolynomial.zeroLocus ℂ V.ideal.toIdeal)
    (hwH : MvPolynomial.eval w H ≠ 0)
    (v : CoordinateVector n) (hv : v ≠ 0)
    (hfv : f.onPoints (Projectivization.mk ℂ v hv) = Projectivization.mk ℂ w hw) :
    v 0 ≠ 0 := by
  rw [f.onPoints_mk] at hfv
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp hfv.symm
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ) hq
  have he : f.evalVector (b • v) = w := by
    rw [f.evalVector_smul, hb]
    exact ha
  have hbV : b • v ∈ MvPolynomial.zeroLocus ℂ V.ideal.toIdeal := by
    rw [← projective_total_invariance_cone f V (Nat.ne_of_gt hq) hV]
    change f.evalVector (b • v) ∈ MvPolynomial.zeroLocus ℂ V.ideal.toIdeal
    rwa [he]
  have hbH : MvPolynomial.eval (f.evalVector (b • v)) H ≠ 0 := by rwa [he]
  have hb0 := projectiveCone_chart_avoidance_eval f V H C hrel (b • v) hbV hbH
  intro hv0
  apply hb0
  simp [Pi.smul_apply, smul_eq_mul, hv0]

end LinearStudy
