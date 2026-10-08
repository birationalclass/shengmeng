module
public import Linear.RationalCoordinateSandwich
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy

/-- Actual centering of the ORIGINAL target preserves its genuine rational
local quotient map's unramification. Transformed compatibility and prime
relationships are derived; the original denominator is unchanged. -/
theorem rationalPolynomialChartMap_unramified_target_centering
    {K σ : Type*} [Field K]
    (z : σ → K) (p0 : MvPolynomial σ K) (p : σ → MvPolynomial σ K)
    (I Q : Ideal (MvPolynomial σ K)) [Q.IsPrime]
    (J P : Ideal (Localization.Away p0)) [P.IsPrime]
    (hQP : Q = P.comap (rationalPolynomialChartMap p0 p).toRingHom)
    (hφ : I.map (rationalPolynomialChartMap p0 p).toRingHom ≤ J)
    (h : (generalPointLocalQuotientPullback I J P Q
      (rationalPolynomialChartMap p0 p).toRingHom hQP hφ).FormallyUnramified) :
    let E := polynomialTranslation z
    let Q' := Q.comap E.symm.toRingHom
    letI : Q'.IsPrime := inferInstance
    let ψ := rationalPolynomialChartMap p0 (fun i => p i - MvPolynomial.C (z i) * p0)
    ∃ (hQP' : Q' = P.comap ψ.toRingHom) (hψ : (I.map E.toRingHom).map ψ.toRingHom ≤ J),
      (generalPointLocalQuotientPullback (I.map E.toRingHom) J P Q'
        ψ.toRingHom hQP' hψ).FormallyUnramified := by
  intro E Q'
  letI : Q'.IsPrime := inferInstance
  intro ψ
  have hψmap : (rationalPolynomialChartMap p0 p).toRingHom.comp E.symm.toRingHom =
      ψ.toRingHom :=
    (congrArg AlgHom.toRingHom (rational_target_centering_actual_map z p0 p)).symm
  have hQP' : Q' = P.comap ψ.toRingHom := by
    change Q.comap E.symm.toRingHom = _
    rw [hQP, Ideal.comap_comap, hψmap]
  have hQ : Q = Q'.comap E.toRingHom := by
    ext F
    change F ∈ Q ↔ E.symm (E F) ∈ Q
    rw [AlgEquiv.symm_apply_apply]
  have hsquare : ψ.toRingHom.comp E.toRingHom =
      (rationalPolynomialChartMap p0 p).toRingHom :=
    rational_target_centering_actual_square z p0 p
  have hψ : (I.map E.toRingHom).map ψ.toRingHom ≤ J := by
    rw [Ideal.map_map, hsquare]
    exact hφ
  let D := RingEquiv.refl (Localization.Away p0)
  have hP : P = P.comap D.toRingHom := by simp [D]
  have hψ' : (I.map E.toRingHom).map ψ.toRingHom ≤ J.map D.toRingHom := by
    simpa [D] using hψ
  have hd : D.toRingHom.comp (rationalPolynomialChartMap p0 p).toRingHom =
      ψ.toRingHom.comp E.toRingHom := by
    rw [hsquare]
    simp [D]
  have hu := generalPointLocalQuotientPullback_unramified_coordinates I Q J P
    Q' P E.toRingEquiv D hQ hP (rationalPolynomialChartMap p0 p).toRingHom
    ψ.toRingHom hQP hQP' hφ hψ' hd h
  refine ⟨hQP', hψ, ?_⟩
  have hJd : J.map D.toRingHom = J := by simp [D]
  have htransport (J' : Ideal (Localization.Away p0)) (hJ' : J.map D.toRingHom = J')
      (hIJ : (I.map E.toRingHom).map ψ.toRingHom ≤ J') :
      (generalPointLocalQuotientPullback (I.map E.toRingHom) J' P Q'
        ψ.toRingHom hQP' hIJ).FormallyUnramified := by
    subst J'
    exact hu
  exact htransport J hJd hψ

end LinearStudy
