module
public import Linear.ProjectiveGeneralReducedFibers
public import Linear.ProjectiveCoordinateUnramified
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace LinearStudy
variable {n : ℕ}

/-- Coordinate evaluation identifies the ACTUAL quotient prime of the
specified original point. No kernel comparison is supplied. -/
theorem IntegralProjectiveEquations.affinePoint_eq_rationalPoint_of_evaluation
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (ρ : (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) →ₐ[ℂ] ℂ)
    (heval : ρ.comp (Ideal.Quotient.mkₐ ℂ V.affineIdeal) = MvPolynomial.aeval x) :
    V.affinePoint x hx = rationalPointPrime ρ := by
  apply PrimeSpectrum.ext
  apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk V.affineIdeal) Ideal.Quotient.mk_surjective
  change (V.affinePointIdeal x).comap (Ideal.Quotient.mk V.affineIdeal) =
    (RingHom.ker ρ.toRingHom).comap (Ideal.Quotient.mk V.affineIdeal)
  rw [V.affinePointIdeal_comap x hx, RingHom.comap_ker]
  exact congrArg (fun ψ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ => RingHom.ker ψ.toRingHom) heval.symm

/-- EVERY actual coordinate point of a WHOLE original fiber over the good
target open is smooth, has the SAME smooth image and is unramified for the
actual original chart pullback. Evaluation is identified with that target,
rather than with an independently chosen rational point. -/
theorem projective_whole_fiber_point_actual_good_loci
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet)
    (b : MvPolynomial (Fin n) ℂ)
    (hgood : let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
      let A := Localization.Away (projectiveChartDenominator f V)
      let φ := projectiveChartOpenMap f V hq hf hV x0 hx0
      letI : Algebra B A := φ.toRingHom.toAlgebra
      ∀ P : PrimeSpectrum A, φ (Ideal.Quotient.mk V.affineIdeal b) ∉ P.asIdeal →
        P ∈ Algebra.smoothLocus ℂ A ∧
        PrimeSpectrum.comap φ.toRingHom P ∈ Algebra.smoothLocus ℂ B ∧
        P ∈ Algebra.unramifiedLocus B A)
    (y z : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet)
    (hz : normalizedProjectivePoint z ∈ V.zeroSet) (hb : MvPolynomial.eval y b ≠ 0)
    (hfy : f.onPoints (normalizedProjectivePoint z) = normalizedProjectivePoint y) :
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let A := Localization.Away (projectiveChartDenominator f V)
    let φ := projectiveChartOpenMap f V hq hf hV x0 hx0
    letI : Algebra B A := φ.toRingHom.toAlgebra
    ∃ hp0 : MvPolynomial.eval z (affineChartPolynomialMap (f.forms 0)) ≠ 0,
      Algebra.IsSmoothAt ℂ (V.affinePoint z hz).asIdeal ∧
      Algebra.IsSmoothAt ℂ (V.affinePoint y hy).asIdeal ∧
      rationalPointPrime (projectiveChartPointEvaluation f V z hz hp0) ∈ Algebra.unramifiedLocus B A ∧
      ((projectiveChartPointEvaluation f V z hz hp0).comp φ).comp
        (Ideal.Quotient.mkₐ ℂ V.affineIdeal) = MvPolynomial.aeval y := by
  intro B A φ
  let ι := IsScalarTower.toAlgHom ℂ B A
  letI : Algebra B A := φ.toRingHom.toAlgebra
  have hzF := projectiveAffineFiberIdeal_mem_of_point f V y z hz hfy
  have hp0 := (projectiveAffineFiberIdeal_point f V y z hzF).2.1
  let ρ := projectiveChartPointEvaluation f V z hz hp0
  have hs := projectiveChartPointEvaluation_source_coordinates f V z hz hp0
  change (ρ.comp ι).comp (Ideal.Quotient.mkₐ ℂ V.affineIdeal) = MvPolynomial.aeval z at hs
  have hi := (projectiveChartOpenMap_rational_point_coordinates f V hq hf hV x0 hx0 ρ z hs).2
  have hrat : (fun i : Fin n => MvPolynomial.eval z (affineChartPolynomialMap (f.forms i.succ)) /
      MvPolynomial.eval z (affineChartPolynomialMap (f.forms 0))) = y := by
    funext i
    apply (div_eq_iff hp0).mpr
    have h := hzF _ ((show Ideal.span (Set.range (fun j : Fin n =>
        affineChartPolynomialMap (f.forms j.succ) -
          MvPolynomial.C (y j) * affineChartPolynomialMap (f.forms 0))) ≤
          projectiveAffineFiberIdeal f V y from le_sup_right)
      (Ideal.subset_span (Set.mem_range_self i)))
    change MvPolynomial.eval z _ = 0 at h
    simpa only [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_C, sub_eq_zero] using h
  rw [hrat] at hi
  have hρb : φ (Ideal.Quotient.mk V.affineIdeal b) ∉ (rationalPointPrime ρ).asIdeal := by
    change ρ (φ (Ideal.Quotient.mk V.affineIdeal b)) ≠ 0
    exact fun h => hb ((AlgHom.congr_fun hi b).symm.trans h)
  obtain ⟨hsource, himage, hunram⟩ := hgood (rationalPointPrime ρ) hρb
  refine ⟨hp0, ?_, ?_, hunram, hi⟩
  · change V.affinePoint z hz ∈ Algebra.smoothLocus ℂ B
    rw [V.affinePoint_eq_rationalPoint_of_evaluation z hz (ρ.comp ι) hs]
    exact rationalPoint_away_smooth_base (projectiveChartDenominator f V) ρ hsource
  · change V.affinePoint y hy ∈ Algebra.smoothLocus ℂ B
    rw [V.affinePoint_eq_rationalPoint_of_evaluation y hy (ρ.comp φ) hi]
    exact himage

end LinearStudy
