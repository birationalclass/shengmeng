module
public import Linear.RationalPointLocalization
public import Linear.AffineRationalPointValues
public import Linear.ProjectiveChartGoodPoint
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
variable {n : ℕ}

/-- The constructed point's image is evaluated by the actual coordinate ratios. -/
theorem projectiveChartOpenMap_rational_point_coordinates
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x0 : Fin n → ℂ)
    (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet)
    (ρ : Localization.Away (projectiveChartDenominator f V) →ₐ[ℂ] ℂ)
    (x : Fin n → ℂ)
    (hx : (ρ.comp (IsScalarTower.toAlgHom ℂ
      (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) (Localization.Away (projectiveChartDenominator f V)))).comp
        (Ideal.Quotient.mkₐ ℂ V.affineIdeal) = MvPolynomial.aeval x) :
    let p0 := affineChartPolynomialMap (f.forms 0)
    let p := fun i : Fin n => affineChartPolynomialMap (f.forms i.succ)
    MvPolynomial.eval x p0 ≠ 0 ∧
      (ρ.comp (projectiveChartOpenMap f V hq hf hV x0 hx0)).comp
        (Ideal.Quotient.mkₐ ℂ V.affineIdeal) =
      MvPolynomial.aeval (fun i => MvPolynomial.eval x (p i) / MvPolynomial.eval x p0) := by
  intro p0 p
  have heval : ∀ H : MvPolynomial (Fin n) ℂ,
      ρ (algebraMap _ (Localization.Away (projectiveChartDenominator f V))
        (Ideal.Quotient.mk V.affineIdeal H)) = MvPolynomial.eval x H := by
    intro H
    exact AlgHom.congr_fun hx H
  have hp0 : MvPolynomial.eval x p0 ≠ 0 := by
    rw [← heval]
    exact rationalPoint_away_denominator_ne_zero (projectiveChartDenominator f V) ρ
  refine ⟨hp0, ?_⟩
  apply MvPolynomial.algHom_ext
  intro i
  change ρ (projectiveChartOpenMap f V hq hf hV x0 hx0
    (Ideal.Quotient.mk V.affineIdeal (MvPolynomial.X i))) = _
  rw [projectiveChartOpenMap_mk]
  simp only [projectiveChartOpenPolynomialMap, MvPolynomial.aeval_X, map_mul]
  change ρ (algebraMap _ (Localization.Away (projectiveChartDenominator f V))
      (Ideal.Quotient.mk V.affineIdeal (p i))) *
    ρ (IsLocalization.Away.invSelf (projectiveChartDenominator f V)) =
      MvPolynomial.eval x (p i) / MvPolynomial.eval x p0
  have hinv := rationalPoint_away_invSelf (projectiveChartDenominator f V) ρ
  change ρ (IsLocalization.Away.invSelf (projectiveChartDenominator f V)) =
    (ρ (algebraMap _ (Localization.Away (projectiveChartDenominator f V))
      (Ideal.Quotient.mk V.affineIdeal p0)))⁻¹ at hinv
  rw [heval] at hinv
  exact congrArg₂ (fun a b : ℂ => a * b) (heval (p i)) hinv

/-- Both smooth points are actual normalized projective points of V, and their
affine coordinate values are linked by f_i/f_0. Unramification holds at the SAME source. -/
theorem projectiveChartOpenMap_exists_good_affine_coordinates
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x0 : Fin n → ℂ)
    (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let A := Localization.Away (projectiveChartDenominator f V)
    let φ := projectiveChartOpenMap f V hq hf hV x0 hx0
    let ι := IsScalarTower.toAlgHom ℂ B A
    letI : Algebra B A := φ.toRingHom.toAlgebra
    ∃ (ρ : A →ₐ[ℂ] ℂ) (x : Fin n → ℂ) (hx : normalizedProjectivePoint x ∈ V.zeroSet)
      (hp0 : MvPolynomial.eval x (affineChartPolynomialMap (f.forms 0)) ≠ 0),
      let y := fun i : Fin n => MvPolynomial.eval x (affineChartPolynomialMap (f.forms i.succ)) /
        MvPolynomial.eval x (affineChartPolynomialMap (f.forms 0))
      ∃ hy : normalizedProjectivePoint y ∈ V.zeroSet,
        Algebra.IsSmoothAt ℂ (V.affinePoint x hx).asIdeal ∧
        Algebra.IsSmoothAt ℂ (V.affinePoint y hy).asIdeal ∧
        rationalPointPrime ρ ∈ Algebra.unramifiedLocus B A ∧
        (ρ.comp ι).comp (Ideal.Quotient.mkₐ ℂ V.affineIdeal) =
          MvPolynomial.aeval x ∧
        (ρ.comp φ).comp (Ideal.Quotient.mkₐ ℂ V.affineIdeal) = MvPolynomial.aeval y := by
  intro B A φ ι
  letI : Algebra B A := φ.toRingHom.toAlgebra
  obtain ⟨ρ, hsource, himage, hunram⟩ := projectiveChartOpenMap_exists_good_rational_point f V hq hf hV x0 hx0
  let σ := ρ.comp ι
  obtain ⟨x, hx, hpoint, heval⟩ := V.affineAlgHom_point_evaluation σ
  obtain ⟨hp0, himageEval⟩ := projectiveChartOpenMap_rational_point_coordinates f V hq hf hV x0 hx0 ρ x heval
  let y := fun i : Fin n => MvPolynomial.eval x (affineChartPolynomialMap (f.forms i.succ)) /
    MvPolynomial.eval x (affineChartPolynomialMap (f.forms 0))
  have hy := projective_total_invariance_affine_image_mem f V hV x hx hp0
  have hpoint' : V.affinePoint x hx = rationalPointPrime σ := PrimeSpectrum.ext hpoint
  have hpointImage : V.affinePoint y hy = rationalPointPrime (ρ.comp φ) := by
    apply PrimeSpectrum.ext
    apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk V.affineIdeal) Ideal.Quotient.mk_surjective
    change (V.affinePointIdeal y).comap (Ideal.Quotient.mk V.affineIdeal) =
      (RingHom.ker (ρ.comp φ).toRingHom).comap (Ideal.Quotient.mk V.affineIdeal)
    rw [V.affinePointIdeal_comap y hy, RingHom.comap_ker]
    exact congrArg (fun ψ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ => RingHom.ker ψ.toRingHom) himageEval.symm
  refine ⟨ρ, x, hx, hp0, hy, ?_, ?_, hunram, heval, himageEval⟩
  · change V.affinePoint x hx ∈ Algebra.smoothLocus ℂ B
    rw [hpoint']
    exact rationalPoint_away_smooth_base (projectiveChartDenominator f V) ρ hsource
  · change V.affinePoint y hy ∈ Algebra.smoothLocus ℂ B
    rw [hpointImage]
    exact himage

end LinearStudy
