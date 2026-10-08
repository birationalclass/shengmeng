module
public import Linear.ProjectiveAffineFiberReduced
public import Linear.ProjectiveNormalizedConePoint
public import Linear.ProjectiveWholeFiberGoodPoint
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- From the original f,V, construct a target whose ENTIRE projective point
fiber lies in one chart. Its actual affine fiber-equation quotient is finite
dimensional and reduced. The number of points is not assumed or computed. -/
theorem projective_exists_whole_reduced_fiber
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x0 : Fin n → ℂ)
    (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ (y : Fin n → ℂ), normalizedProjectivePoint y ∈ V.zeroSet ∧
      (f.onPoints ⁻¹' {normalizedProjectivePoint y}).Finite ∧
      (∀ (v : CoordinateVector n) (hv : v ≠ 0),
        f.onPoints (Projectivization.mk ℂ v hv) = normalizedProjectivePoint y → v 0 ≠ 0) ∧
      Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal f V y) ∧
      IsReduced (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal f V y) := by
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let A := Localization.Away (projectiveChartDenominator f V)
  let φ := projectiveChartOpenMap f V hq hf hV x0 hx0
  letI : Algebra B A := φ.toRingHom.toAlgebra
  obtain ⟨b, hb, _, hgood⟩ := projectiveChartOpenMap_exists_target_good_loci f V hq hf hV x0 hx0
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective b
  have hpI : p ∉ V.affineIdeal := by
    intro h
    exact hb (hp.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr h))
  obtain ⟨H, C, hH, hrel⟩ := projectiveConeMap_exists_chart_avoidance_polynomial f V hq hf hV x0 hx0
  obtain ⟨w, hwV, hw0, hwH, hwp⟩ := projectiveCone_exists_target_chart_open_point V x0 hx0 H hH p hpI
  let y : Fin n → ℂ := fun i => w i.succ / w 0
  have hy : normalizedProjectivePoint y ∈ V.zeroSet := V.normalizedConePoint_mem w hwV hw0
  have hw : w ≠ 0 := by
    intro h
    exact hw0 (congrFun h 0)
  have hynorm := normalizedProjectivePoint_coordinate_ratios w hw hw0
  refine ⟨y, hy, f.onPoints_fibers_finite hq _, ?_, projectiveAffineFiberQuotient_finite f V hq y, ?_⟩
  · intro v hv hfv
    rw [hynorm] at hfv
    exact projectiveWholeFiber_chart_avoidance f V hq hV H C hrel w hw hwV hwH v hv hfv
  · have hρb : V.affinePointEvaluation y hy b ≠ 0 := by
      rw [← hp, V.affinePointEvaluation_mk]
      exact hwp
    apply projectiveAffineFiberQuotient_isReduced_of_target_open f V hq hf hV y hy b hρb
    dsimp only
    intro P hP
    exact (hgood P hP).2.2

end LinearStudy
