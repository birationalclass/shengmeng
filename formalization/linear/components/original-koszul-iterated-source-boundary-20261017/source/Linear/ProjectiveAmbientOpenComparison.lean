module
public import Linear.AwayQuotientComparison
public import Linear.ProjectiveChartOpenMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace LinearStudy
variable {n : ℕ}

theorem projectiveChartOpenPolynomialMap_ambient_comp
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) :
    let p0 := affineChartPolynomialMap (f.forms 0)
    let p := fun i : Fin n => affineChartPolynomialMap (f.forms i.succ)
    let J := V.affineIdeal.map (algebraMap _ (Localization.Away p0))
    (awayQuotientEquiv V.affineIdeal p0).toRingHom.comp
      ((Ideal.Quotient.mk J).comp (rationalPolynomialChartMap p0 p).toRingHom) =
        (projectiveChartOpenPolynomialMap f V).toRingHom := by
  intro p0 p J
  exact congrArg AlgHom.toRingHom (rationalPolynomialChartMap_awayQuotient_comp V.affineIdeal p0 p)

/-- The actual ambient ratio map preserves the equation ideal after denominator localization. -/
theorem projectiveRationalPolynomialChartMap_ideal
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    let p0 := affineChartPolynomialMap (f.forms 0)
    let p := fun i : Fin n => affineChartPolynomialMap (f.forms i.succ)
    V.affineIdeal.map (rationalPolynomialChartMap p0 p).toRingHom ≤
      V.affineIdeal.map (algebraMap _ (Localization.Away p0)) := by
  intro p0 p
  apply Ideal.map_le_iff_le_comap.mpr
  intro H hH
  change rationalPolynomialChartMap p0 p H ∈
    V.affineIdeal.map (algebraMap _ (Localization.Away p0))
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (awayQuotientEquiv V.affineIdeal p0).injective
  rw [map_zero]
  have he := RingHom.congr_fun (projectiveChartOpenPolynomialMap_ambient_comp f V) H
  change awayQuotientEquiv V.affineIdeal p0
    (Ideal.Quotient.mk _ (rationalPolynomialChartMap p0 p H)) =
      projectiveChartOpenPolynomialMap f V H at he
  rw [he]
  exact RingHom.mem_ker.mp (projectiveChartOpenPolynomialMap_ideal f V hq hf hV x hx hH)

/-- The induced ambient quotient map agrees with the actual variety chart map. -/
theorem projectiveChartOpenMap_ambient_quotient_comp
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    let p0 := affineChartPolynomialMap (f.forms 0)
    let p := fun i : Fin n => affineChartPolynomialMap (f.forms i.succ)
    let J := V.affineIdeal.map (algebraMap _ (Localization.Away p0))
    (awayQuotientEquiv V.affineIdeal p0).toRingHom.comp
      (Ideal.quotientMap J (rationalPolynomialChartMap p0 p).toRingHom
        (Ideal.map_le_iff_le_comap.mp (projectiveRationalPolynomialChartMap_ideal f V hq hf hV x hx))) =
      (projectiveChartOpenMap f V hq hf hV x hx).toRingHom := by
  intro p0 p J
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro H
  change awayQuotientEquiv V.affineIdeal p0
    (Ideal.Quotient.mk J (rationalPolynomialChartMap p0 p H)) =
      projectiveChartOpenMap f V hq hf hV x hx (Ideal.Quotient.mk V.affineIdeal H)
  rw [projectiveChartOpenMap_mk]
  exact RingHom.congr_fun (projectiveChartOpenPolynomialMap_ambient_comp f V) H

end LinearStudy
