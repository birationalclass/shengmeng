module
public import Linear.HomogeneousRationalIdeal
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Total invariance supplies the power sandwich for the actual rational
chart pullback; ideal preservation is a conclusion, not a new hypothesis. -/
theorem projective_total_invariance_rational_chart_sandwich {n : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hf : f.degree ≠ 0) (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    let D := affineChartPolynomialMap (K := ℂ) (n := n)
    let p0 := D (f.forms 0)
    let p := fun i : Fin n => D (f.forms i.succ)
    let I := V.ideal.toIdeal.map D.toRingHom
    let A := algebraMap _ (Localization.Away p0)
    ∃ e : ℕ, 0 < e ∧
      (I.map A) ^ e ≤ I.map (rationalPolynomialChartMap p0 p).toRingHom ∧
      I.map (rationalPolynomialChartMap p0 p).toRingHom ≤ I.map A := by
  intro D p0 p I A
  have he := homogeneous_projective_chart_pullback_ideal
    V.ideal.toIdeal V.ideal.isHomogeneous f.forms
  change I.map (rationalPolynomialChartMap p0 p).toRingHom =
    (V.ideal.toIdeal.map (MvPolynomial.aeval f.forms).toRingHom).map
      (A.comp D.toRingHom) at he
  obtain ⟨e, hpos, hlo, hhi⟩ := projective_total_invariance_formal_sandwich
    f V hf hV (A.comp D.toRingHom)
  have hi : I.map A = V.ideal.toIdeal.map (A.comp D.toRingHom) :=
    Ideal.map_map _ _
  refine ⟨e, hpos, ?_, ?_⟩
  · rw [he, hi]
    exact hlo
  · rw [he, hi]
    exact hhi

theorem projective_total_invariance_rational_chart_radical {n : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hf : f.degree ≠ 0) (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    {S : Type*} [CommRing S]
    (χ : Localization.Away (affineChartPolynomialMap (f.forms 0)) →+* S) :
    let D := affineChartPolynomialMap (K := ℂ) (n := n)
    let p0 := D (f.forms 0)
    let p := fun i : Fin n => D (f.forms i.succ)
    let I := V.ideal.toIdeal.map D.toRingHom
    ((I.map (rationalPolynomialChartMap p0 p).toRingHom).map χ).radical =
      ((I.map (algebraMap _ (Localization.Away p0))).map χ).radical := by
  intro D p0 p I
  obtain ⟨e, hpos, hlo, hhi⟩ :=
    projective_total_invariance_rational_chart_sandwich f V hf hV
  apply le_antisymm
  · exact Ideal.radical_mono (Ideal.map_mono hhi)
  · have h := Ideal.radical_mono (Ideal.map_mono (f := χ) hlo)
    rw [Ideal.map_pow, Ideal.radical_pow _ (Nat.ne_of_gt hpos)] at h
    exact h

end LinearStudy
