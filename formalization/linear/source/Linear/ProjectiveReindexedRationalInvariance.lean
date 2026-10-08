module
public import Linear.RationalReindexedSourceCoordinates
public import Linear.ProjectiveRationalInvariance
public import Linear.ProjectiveAffineVariety
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

/-- For the ORIGINAL totally invariant variety and ORIGINAL homogeneous
map, arbitrary independent source coordinates and target reindexing carry
the SAME actual rational ideal-power sandwich. Neither inequality is input. -/
theorem projective_original_reindexed_rational_power_sandwich
    {n : ℕ} {τ : Type*}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hf : f.degree ≠ 0) (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (E : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial τ ℂ) (b : Fin n ≃ τ) :
    let p0 := E (affineChartPolynomialMap (f.forms 0))
    let p := fun j => E (affineChartPolynomialMap (f.forms (b.symm j).succ))
    let I := V.affineIdeal.map (MvPolynomial.renameEquiv ℂ b).toRingHom
    let J := V.affineIdeal.map E.toRingHom
    ∃ e : ℕ, 0 < e ∧
      (J.map (algebraMap _ (Localization.Away p0))) ^ e ≤
        I.map (rationalPolynomialChartMap p0 p).toRingHom ∧
      I.map (rationalPolynomialChartMap p0 p).toRingHom ≤
        J.map (algebraMap _ (Localization.Away p0)) := by
  intro p0 p I J
  obtain ⟨e, he, hlo, hhi⟩ := projective_total_invariance_rational_chart_sandwich f V hf hV
  obtain ⟨hlo',hhi'⟩ := rational_source_coordinates_target_reindex_power_sandwich
    E b (affineChartPolynomialMap (f.forms 0))
    (fun i => affineChartPolynomialMap (f.forms i.succ)) V.affineIdeal V.affineIdeal e hlo hhi
  exact ⟨e,he,hlo',hhi'⟩

end LinearStudy
