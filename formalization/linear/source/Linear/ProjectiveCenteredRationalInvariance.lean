module
public import Linear.ProjectiveReindexedRationalInvariance
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open scoped Matrix
attribute [local instance] MvPolynomial.gradedAlgebra

theorem rational_target_linear_coordinates_actual_power_sandwich
    {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]
    (M : Matrix σ σ K) (hM : Matrix.det M ≠ 0)
    (p0 : MvPolynomial σ K) (p : σ → MvPolynomial σ K)
    (I : Ideal (MvPolynomial σ K)) (J : Ideal (Localization.Away p0))
    (m : ℕ) (hlo : J ^ m ≤ I.map (rationalPolynomialChartMap p0 p).toRingHom)
    (hhi : I.map (rationalPolynomialChartMap p0 p).toRingHom ≤ J) :
    J ^ m ≤ (I.map (polynomialLinearChangeEquiv M hM).toRingHom).map
        (rationalPolynomialChartMap p0
          (fun i => MvPolynomial.aeval p ((M⁻¹).toMvPolynomial i))).toRingHom ∧
      (I.map (polynomialLinearChangeEquiv M hM).toRingHom).map
        (rationalPolynomialChartMap p0
          (fun i => MvPolynomial.aeval p ((M⁻¹).toMvPolynomial i))).toRingHom ≤ J := by
  let E := polynomialLinearChangeEquiv M hM
  let ψ := rationalPolynomialChartMap p0
    (fun i => MvPolynomial.aeval p ((M⁻¹).toMvPolynomial i))
  have hψ : ψ = (rationalPolynomialChartMap p0 p).comp E.symm.toAlgHom :=
    rationalPolynomialChartMap_target_linear_coordinates M⁻¹ p0 p
  have hsquare : ψ.toRingHom.comp E.toRingHom = (rationalPolynomialChartMap p0 p).toRingHom := by
    rw [hψ]
    apply RingHom.ext
    intro F
    change rationalPolynomialChartMap p0 p (E.symm (E F)) = rationalPolynomialChartMap p0 p F
    rw [E.symm_apply_apply]
  have heq : (I.map E.toRingHom).map ψ.toRingHom =
      I.map (rationalPolynomialChartMap p0 p).toRingHom := by
    rw [Ideal.map_map, hsquare]
  change J ^ m ≤ (I.map E.toRingHom).map ψ.toRingHom ∧ _
  rw [heq]
  exact ⟨hlo,hhi⟩

/-- Actual independent source coordinates, target linear normalization and
target centering of the ORIGINAL f,V construct the same power sandwich.
No inequality for either original or transformed ideal is supplied. -/
theorem projective_original_centered_rational_power_sandwich
    {n : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hf : f.degree ≠ 0) (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (E : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial τ ℂ) (b : Fin n ≃ τ)
    (M : Matrix τ τ ℂ) (hM : Matrix.det M ≠ 0) (z : τ → ℂ) :
    let p0 := E (affineChartPolynomialMap (f.forms 0))
    let p := fun j => E (affineChartPolynomialMap (f.forms (b.symm j).succ))
    let pL := fun i => MvPolynomial.aeval p ((M⁻¹).toMvPolynomial i)
    let pC := fun i => pL i - MvPolynomial.C (z i) * p0
    let I := ((V.affineIdeal.map (MvPolynomial.renameEquiv ℂ b).toRingHom).map
      (polynomialLinearChangeEquiv M hM).toRingHom).map (polynomialTranslation z).toRingHom
    let J := V.affineIdeal.map E.toRingHom
    ∃ e : ℕ, 0 < e ∧
      (J.map (algebraMap _ (Localization.Away p0))) ^ e ≤
        I.map (rationalPolynomialChartMap p0 pC).toRingHom ∧
      I.map (rationalPolynomialChartMap p0 pC).toRingHom ≤
        J.map (algebraMap _ (Localization.Away p0)) := by
  intro p0 p pL pC I J
  obtain ⟨e,he,hlo,hhi⟩ := projective_original_reindexed_rational_power_sandwich f V hf hV E b
  obtain ⟨hloL,hhiL⟩ := rational_target_linear_coordinates_actual_power_sandwich M hM
    p0 p (V.affineIdeal.map (MvPolynomial.renameEquiv ℂ b).toRingHom)
    (J.map (algebraMap _ (Localization.Away p0))) e hlo hhi
  obtain ⟨hloC,hhiC⟩ := rational_target_centering_actual_power_sandwich z p0 pL
    ((V.affineIdeal.map (MvPolynomial.renameEquiv ℂ b).toRingHom).map
      (polynomialLinearChangeEquiv M hM).toRingHom)
    (J.map (algebraMap _ (Localization.Away p0))) e hloL hhiL
  exact ⟨e,he,hloC,hhiC⟩

end LinearStudy
