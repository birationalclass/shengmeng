module
public import Linear.ProjectiveWholeFiberChart
public import Linear.ProjectiveConeGoodTargetPoint
public import Linear.ProjectiveChartPointEvaluation
public import Linear.ProjectiveTargetGoodLoci
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- The original projective map has a target point whose ENTIRE finite
fiber lies in one source chart; all those chart points have smooth source,
smooth image and actual unramification for the original pullback. This does
not yet compute the number of points or prove scheme-fiber reducedness. -/
theorem projective_exists_whole_fiber_good_target_point
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x0 : Fin n → ℂ)
    (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let A := Localization.Away (projectiveChartDenominator f V)
    let φ := projectiveChartOpenMap f V hq hf hV x0 hx0
    let ι := IsScalarTower.toAlgHom ℂ B A
    letI : Algebra B A := φ.toRingHom.toAlgebra
    ∃ (w : CoordinateVector n) (hw : w ≠ 0),
      w ∈ MvPolynomial.zeroLocus ℂ V.ideal.toIdeal ∧
      (f.onPoints ⁻¹' {Projectivization.mk ℂ w hw}).Finite ∧
      (∀ (v : CoordinateVector n) (hv : v ≠ 0),
        f.onPoints (Projectivization.mk ℂ v hv) = Projectivization.mk ℂ w hw → v 0 ≠ 0) ∧
      ∀ (z : Fin n → ℂ) (hz : normalizedProjectivePoint z ∈ V.zeroSet),
        f.onPoints (normalizedProjectivePoint z) = Projectivization.mk ℂ w hw →
        ∃ hp0 : MvPolynomial.eval z (affineChartPolynomialMap (f.forms 0)) ≠ 0,
          let ρ := projectiveChartPointEvaluation f V z hz hp0
          rationalPointPrime ρ ∈ Algebra.smoothLocus ℂ A ∧
          rationalPointPrime (ρ.comp φ) ∈ Algebra.smoothLocus ℂ B ∧
          rationalPointPrime ρ ∈ Algebra.unramifiedLocus B A ∧
          (ρ.comp ι).comp (Ideal.Quotient.mkₐ ℂ V.affineIdeal) = MvPolynomial.aeval z := by
  intro B A φ ι
  letI : Algebra B A := φ.toRingHom.toAlgebra
  obtain ⟨b, hb, _, hgood⟩ := projectiveChartOpenMap_exists_target_good_loci f V hq hf hV x0 hx0
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective b
  have hpI : p ∉ V.affineIdeal := by
    intro h
    exact hb (hp.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr h))
  obtain ⟨H, C, hH, hrel⟩ := projectiveConeMap_exists_chart_avoidance_polynomial f V hq hf hV x0 hx0
  obtain ⟨w, hwV, hw0, hwH, hwp⟩ := projectiveCone_exists_target_chart_open_point V x0 hx0 H hH p hpI
  have hw : w ≠ 0 := by
    intro h
    exact hw0 (congrFun h 0)
  refine ⟨w, hw, hwV, f.onPoints_fibers_finite hq _, ?_, ?_⟩
  · intro v hv hfv
    exact projectiveWholeFiber_chart_avoidance f V hq hV H C hrel w hw hwV hwH v hv hfv
  · intro z hz hfw
    change f.onPoints (Projectivization.mk ℂ (Fin.cases 1 z) _) = Projectivization.mk ℂ w hw at hfw
    rw [f.onPoints_mk] at hfw
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp hfw.symm
    let fv := f.evalVector (Fin.cases 1 z)
    have heval : ∀ i, MvPolynomial.eval z (affineChartPolynomialMap (f.forms i)) = fv i := by
      intro i
      exact AlgHom.congr_fun (affineChartPolynomialMap_comp_aeval (K := ℂ) z) (f.forms i)
    have h0 : (a : ℂ) * fv 0 = w 0 := congrFun ha 0
    have hp0 : MvPolynomial.eval z (affineChartPolynomialMap (f.forms 0)) ≠ 0 := by
      intro hzero
      apply hw0
      rw [← h0, ← heval 0, hzero, mul_zero]
    let ρ := projectiveChartPointEvaluation f V z hz hp0
    have hs := projectiveChartPointEvaluation_source_coordinates f V z hz hp0
    change (ρ.comp ι).comp (Ideal.Quotient.mkₐ ℂ V.affineIdeal) = MvPolynomial.aeval z at hs
    have hi := (projectiveChartOpenMap_rational_point_coordinates f V hq hf hV x0 hx0 ρ z hs).2
    have hrat : (fun i : Fin n => MvPolynomial.eval z (affineChartPolynomialMap (f.forms i.succ)) /
        MvPolynomial.eval z (affineChartPolynomialMap (f.forms 0))) =
        (fun i : Fin n => w i.succ / w 0) := by
      funext i
      have hsu : (a : ℂ) * fv i.succ = w i.succ := congrFun ha i.succ
      apply (div_eq_div_iff hp0 hw0).mpr
      rw [heval i.succ, heval 0, ← h0, ← hsu]
      ring
    rw [hrat] at hi
    have hρb : ρ (φ b) ≠ 0 := by
      rw [← hp]
      exact (AlgHom.congr_fun hi p).symm ▸ hwp
    have hprime : φ b ∉ (rationalPointPrime ρ).asIdeal := hρb
    obtain ⟨hsource, himage, hunram⟩ := hgood (rationalPointPrime ρ) hprime
    refine ⟨hp0, hsource, ?_, hunram, hs⟩
    change PrimeSpectrum.comap φ.toRingHom (rationalPointPrime ρ) ∈ Algebra.smoothLocus ℂ B at himage
    exact himage

end LinearStudy
