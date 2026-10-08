module
public import Linear.ProjectiveHomogeneousChartAvoidance
public import Linear.ProjectiveWholeFiberPointCount
public import Linear.ProjectiveCommonChart
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- A nonempty actual affine target PRINCIPAL OPEN whose EVERY whole
projective fiber has a reduced finite-dimensional equation quotient and
exact point/dimension equality. No generic good-fiber assumption is used. -/
theorem projective_exists_general_whole_reduced_fibers
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x0 : Fin n → ℂ)
    (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    ∃ p : MvPolynomial (Fin n) ℂ, p ∉ V.affineIdeal ∧
      (let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
       let A := Localization.Away (projectiveChartDenominator f V)
       let φ := projectiveChartOpenMap f V hq hf hV x0 hx0
       letI : Algebra B A := φ.toRingHom.toAlgebra
       ∀ P : PrimeSpectrum A,
         φ (Ideal.Quotient.mk V.affineIdeal p) ∉ P.asIdeal →
         P ∈ Algebra.smoothLocus ℂ A ∧
         PrimeSpectrum.comap φ.toRingHom P ∈ Algebra.smoothLocus ℂ B ∧
         P ∈ Algebra.unramifiedLocus B A) ∧
      (∃ y : Fin n → ℂ, normalizedProjectivePoint y ∈ V.zeroSet ∧ MvPolynomial.eval y p ≠ 0) ∧
      ∀ (y : Fin n → ℂ), normalizedProjectivePoint y ∈ V.zeroSet → MvPolynomial.eval y p ≠ 0 →
        (f.onPoints ⁻¹' {normalizedProjectivePoint y}).Finite ∧
        (∀ (v : CoordinateVector n) (hv : v ≠ 0),
          f.onPoints (Projectivization.mk ℂ v hv) = normalizedProjectivePoint y → v 0 ≠ 0) ∧
        Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal f V y) ∧
        IsReduced (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal f V y) ∧
        Nat.card (f.onPoints ⁻¹' {normalizedProjectivePoint y}) =
          Module.finrank ℂ (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal f V y) := by
  letI := V.prime
  letI := V.affineIdeal_isPrime_of_point x0 hx0
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let A := Localization.Away (projectiveChartDenominator f V)
  let φ := projectiveChartOpenMap f V hq hf hV x0 hx0
  letI : Algebra B A := φ.toRingHom.toAlgebra
  obtain ⟨b, hb, _, hgood⟩ := projectiveChartOpenMap_exists_target_good_loci f V hq hf hV x0 hx0
  obtain ⟨p₀, hp₀⟩ := Ideal.Quotient.mk_surjective b
  have hp₀I : p₀ ∉ V.affineIdeal := by
    intro h
    exact hb (hp₀.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr h))
  obtain ⟨k, H, C, hhom, hH, hrel⟩ :=
    projectiveConeMap_exists_homogeneous_chart_avoidance_polynomial f V hq hf hV x0 hx0
  have hX : (MvPolynomial.X (0 : Fin (n + 1)) : CoordinateRing n) ∉ V.ideal.toIdeal := by
    intro h
    have he := (V.normalizedPoint_mem_iff x0).mp hx0 _ h
    simpa using he
  have hHI : affineChartPolynomialMap H ∉ V.affineIdeal := fun h =>
    hH ((affineChartPolynomialMap_homogeneous_mem_iff V.ideal.toIdeal
      V.ideal.isHomogeneous hX H hhom).mp h)
  let p := affineChartPolynomialMap H * p₀
  have hp : p ∉ V.affineIdeal := by
    intro h
    rcases (show V.affineIdeal.IsPrime from inferInstance).mem_or_mem h with h₁ | h₂
    · exact hHI h₁
    · exact hp₀I h₂
  obtain ⟨y₀, hy₀, hyp, _⟩ := V.exists_smooth_affine_point_avoiding x0 hx0 p hp
  have hgoodp : ∀ P : PrimeSpectrum A,
      φ (Ideal.Quotient.mk V.affineIdeal p) ∉ P.asIdeal →
      P ∈ Algebra.smoothLocus ℂ A ∧
      PrimeSpectrum.comap φ.toRingHom P ∈ Algebra.smoothLocus ℂ B ∧
      P ∈ Algebra.unramifiedLocus B A := by
    intro P hP
    apply hgood P
    intro hbP
    apply hP
    change φ (Ideal.Quotient.mk V.affineIdeal (affineChartPolynomialMap H * p₀)) ∈ P.asIdeal
    rw [map_mul, map_mul, hp₀]
    exact P.asIdeal.mul_mem_left _ hbP
  refine ⟨p, hp, hgoodp, ⟨y₀, hy₀, hyp⟩, ?_⟩
  intro y hy hyp
  have hpvals : MvPolynomial.eval y (affineChartPolynomialMap H) ≠ 0 ∧
      MvPolynomial.eval y p₀ ≠ 0 := by
    exact mul_ne_zero_iff.mp (by simpa only [p, MvPolynomial.eval_mul] using hyp)
  have hchart : ∀ (v : CoordinateVector n) (hv : v ≠ 0),
      f.onPoints (Projectivization.mk ℂ v hv) = normalizedProjectivePoint y → v 0 ≠ 0 := by
    intro v hv hfv
    let w : CoordinateVector n := Fin.cases 1 y
    have hw : w ≠ 0 := normalizedCoordinateVector_ne_zero y
    have hwV : w ∈ MvPolynomial.zeroLocus ℂ V.ideal.toIdeal :=
      (V.normalizedPoint_mem_iff y).mp hy
    have hwH : MvPolynomial.eval w H ≠ 0 := by
      have he := AlgHom.congr_fun (affineChartPolynomialMap_comp_aeval (K := ℂ) y) H
      exact fun hz => hpvals.1 (he.trans hz)
    change f.onPoints (Projectivization.mk ℂ v hv) = Projectivization.mk ℂ w hw at hfv
    exact projectiveWholeFiber_chart_avoidance (n := n) f V hq hV H C hrel w
      hw hwV hwH v hv hfv
  have hfin := projectiveAffineFiberQuotient_finite f V hq y
  have hρb : V.affinePointEvaluation y hy b ≠ 0 := by
    rw [← hp₀, V.affinePointEvaluation_mk]
    exact hpvals.2
  have hred : IsReduced (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal f V y) := by
    apply projectiveAffineFiberQuotient_isReduced_of_target_open f V hq hf hV y hy b hρb
    dsimp only
    intro P hP
    exact (hgood P hP).2.2
  letI := hfin
  letI := hred
  exact ⟨f.onPoints_fibers_finite hq _, hchart, hfin, hred,
    projectiveWholeFiber_card_eq_affine_quotient_finrank f V y hy hV hchart⟩

end LinearStudy
