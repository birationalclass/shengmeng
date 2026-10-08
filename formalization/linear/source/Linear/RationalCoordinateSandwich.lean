module
public import Linear.RationalLinearTargetCoordinates
public import Linear.PolynomialAwayCoordinateEquiv
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace LinearStudy

/-- The actual ambient coordinate diagram transports the original ideal
power inequalities; no transformed inequality is added as an input. -/
theorem ideal_power_sandwich_under_coordinate_diagram
    {R T A C : Type*} [CommRing R] [CommRing T] [CommRing A] [CommRing C]
    (e : R ≃+* T) (d : A ≃+* C) (φ : R →+* A) (ψ : T →+* C)
    (hd : d.toRingHom.comp φ = ψ.comp e.toRingHom)
    (I : Ideal R) (J : Ideal A) (m : ℕ)
    (hlo : J ^ m ≤ I.map φ) (hhi : I.map φ ≤ J) :
    (J.map d.toRingHom) ^ m ≤ (I.map e.toRingHom).map ψ ∧
      (I.map e.toRingHom).map ψ ≤ J.map d.toRingHom := by
  have hEq : (I.map φ).map d.toRingHom = (I.map e.toRingHom).map ψ := by
    rw [Ideal.map_map, hd, Ideal.map_map]
  have hl := Ideal.map_mono (f := d.toRingHom) hlo
  have hh := Ideal.map_mono (f := d.toRingHom) hhi
  rw [Ideal.map_pow, hEq] at hl
  rw [hEq] at hh
  exact ⟨hl, hh⟩

theorem rational_target_centering_actual_map
    {K σ : Type*} [Field K]
    (z : σ → K) (p0 : MvPolynomial σ K) (p : σ → MvPolynomial σ K) :
    rationalPolynomialChartMap p0 (fun i => p i - MvPolynomial.C (z i) * p0) =
      (rationalPolynomialChartMap p0 p).comp (polynomialTranslation z).symm.toAlgHom := by
  have hs : (polynomialTranslation (-z)).toAlgHom =
      (polynomialTranslation z).symm.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [polynomialTranslation, sub_eq_add_neg]
  have h := rationalPolynomialChartMap_target_translation (-z) p0 p
  rw [hs] at h
  simpa only [Pi.neg_apply, map_neg, neg_mul, sub_eq_add_neg] using h

/-- The SAME denominator and centered original numerators implement the
actual target coordinate square, not an independently assumed square. -/
theorem rational_target_centering_actual_square
    {K σ : Type*} [Field K]
    (z : σ → K) (p0 : MvPolynomial σ K) (p : σ → MvPolynomial σ K) :
    (rationalPolynomialChartMap p0 (fun i => p i - MvPolynomial.C (z i) * p0)).toRingHom.comp
      (polynomialTranslation z).toRingHom =
        (rationalPolynomialChartMap p0 p).toRingHom := by
  rw [rational_target_centering_actual_map]
  apply RingHom.ext
  intro F
  change rationalPolynomialChartMap p0 p
    ((polynomialTranslation z).symm (polynomialTranslation z F)) = _
  rw [AlgEquiv.symm_apply_apply]
  rfl

/-- Ideal powers remain valid after actual target centering. -/
theorem rational_target_centering_actual_power_sandwich
    {K σ : Type*} [Field K]
    (z : σ → K) (p0 : MvPolynomial σ K) (p : σ → MvPolynomial σ K)
    (I : Ideal (MvPolynomial σ K)) (J : Ideal (Localization.Away p0))
    (m : ℕ) (hlo : J ^ m ≤ I.map (rationalPolynomialChartMap p0 p).toRingHom)
    (hhi : I.map (rationalPolynomialChartMap p0 p).toRingHom ≤ J) :
    J ^ m ≤ (I.map (polynomialTranslation z).toRingHom).map
        (rationalPolynomialChartMap p0 (fun i => p i - MvPolynomial.C (z i) * p0)).toRingHom ∧
      (I.map (polynomialTranslation z).toRingHom).map
        (rationalPolynomialChartMap p0 (fun i => p i - MvPolynomial.C (z i) * p0)).toRingHom ≤ J := by
  have heq : (I.map (polynomialTranslation z).toRingHom).map
      (rationalPolynomialChartMap p0 (fun i => p i - MvPolynomial.C (z i) * p0)).toRingHom =
      I.map (rationalPolynomialChartMap p0 p).toRingHom := by
    rw [Ideal.map_map, rational_target_centering_actual_square]
  rw [heq]
  exact ⟨hlo,hhi⟩

/-- Source-coordinate changes preserve the actual original ideal-power
sandwich through the ACTUAL changed denominator localization. -/
theorem rational_source_coordinates_actual_power_sandwich
    {K σ : Type*} [Field K]
    (e : MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K)
    (p0 : MvPolynomial σ K) (p : σ → MvPolynomial σ K)
    (I J : Ideal (MvPolynomial σ K)) (m : ℕ)
    (hlo : (J.map (algebraMap _ (Localization.Away p0))) ^ m ≤
      I.map (rationalPolynomialChartMap p0 p).toRingHom)
    (hhi : I.map (rationalPolynomialChartMap p0 p).toRingHom ≤
      J.map (algebraMap _ (Localization.Away p0))) :
    ((J.map e.toRingHom).map (algebraMap _ (Localization.Away (e p0)))) ^ m ≤
      I.map (rationalPolynomialChartMap (e p0) (fun i => e (p i))).toRingHom ∧
    I.map (rationalPolynomialChartMap (e p0) (fun i => e (p i))).toRingHom ≤
      (J.map e.toRingHom).map (algebraMap _ (Localization.Away (e p0))) := by
  let d := polynomialAwayCoordinateEquiv e p0
  have hd : d.toRingHom.comp (rationalPolynomialChartMap p0 p).toRingHom =
      (rationalPolynomialChartMap (e p0) (fun i => e (p i))).toRingHom :=
    congrArg AlgHom.toRingHom (rationalPolynomialChartMap_source_coordinate_equiv e p0 p)
  have hl := Ideal.map_mono (f := d.toRingHom) hlo
  have hh := Ideal.map_mono (f := d.toRingHom) hhi
  have hJ : (J.map (algebraMap _ (Localization.Away p0))).map d.toRingHom =
      (J.map e.toRingHom).map (algebraMap _ (Localization.Away (e p0))) :=
    polynomialAwayCoordinateEquiv_original_ideal e p0 J
  have hmap : (I.map (rationalPolynomialChartMap p0 p).toRingHom).map d.toRingHom =
      I.map (rationalPolynomialChartMap (e p0) (fun i => e (p i))).toRingHom := by
    rw [Ideal.map_map, hd]
  rw [Ideal.map_pow, hJ, hmap] at hl
  rw [hmap, hJ] at hh
  exact ⟨hl, hh⟩

end LinearStudy
