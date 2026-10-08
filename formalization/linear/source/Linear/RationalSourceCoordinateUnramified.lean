module
public import Linear.PolynomialAwayCoordinateEquiv
public import Linear.PointLocalPullbackCoordinateComparison
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy

/-- Source coordinates preserve the ORIGINAL rational point-local map's
unramification. Its transformed prime, ideal compatibility and local-map
diagram are constructed; they are not new geometric assumptions. -/
theorem rationalPolynomialChartMap_unramified_source_coordinates
    {K σ : Type*} [Field K]
    (e : MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K)
    (p0 : MvPolynomial σ K) (p : σ → MvPolynomial σ K)
    (I J Q : Ideal (MvPolynomial σ K)) [Q.IsPrime]
    (P : Ideal (Localization.Away p0)) [P.IsPrime]
    (hQP : Q = P.comap (rationalPolynomialChartMap p0 p).toRingHom)
    (hφ : I.map (rationalPolynomialChartMap p0 p).toRingHom ≤
      J.map (algebraMap _ (Localization.Away p0)))
    (h : (generalPointLocalQuotientPullback I
      (J.map (algebraMap _ (Localization.Away p0))) P Q
        (rationalPolynomialChartMap p0 p).toRingHom hQP hφ).FormallyUnramified) :
    let d := polynomialAwayCoordinateEquiv e p0
    let P' := P.comap d.symm.toRingHom
    letI : P'.IsPrime := inferInstance
    let ψ := rationalPolynomialChartMap (e p0) (fun i => e (p i))
    let J' := (J.map e.toRingHom).map (algebraMap _ (Localization.Away (e p0)))
    ∃ (hQP' : Q = P'.comap ψ.toRingHom) (hψ : I.map ψ.toRingHom ≤ J'),
      (generalPointLocalQuotientPullback I J' P' Q ψ.toRingHom hQP' hψ).FormallyUnramified := by
  intro d P'
  letI : P'.IsPrime := inferInstance
  intro ψ J'
  have hP : P = P'.comap d.toRingHom := by
    ext z
    change z ∈ P ↔ d.symm (d z) ∈ P
    rw [d.symm_apply_apply]
  have hd : d.toRingHom.comp (rationalPolynomialChartMap p0 p).toRingHom = ψ.toRingHom := by
    exact congrArg AlgHom.toRingHom (rationalPolynomialChartMap_source_coordinate_equiv e p0 p)
  have hQP' : Q = P'.comap ψ.toRingHom := by
    calc
      Q = P.comap (rationalPolynomialChartMap p0 p).toRingHom := hQP
      _ = P'.comap ψ.toRingHom := by rw [hP, Ideal.comap_comap, hd]
  have hJ : (J.map (algebraMap _ (Localization.Away p0))).map d.toRingHom = J' :=
    polynomialAwayCoordinateEquiv_original_ideal e p0 J
  have hψ : I.map ψ.toRingHom ≤ J' := by
    have hh := Ideal.map_mono (f := d.toRingHom) hφ
    rw [Ideal.map_map, hd, hJ] at hh
    exact hh
  let E := RingEquiv.refl (MvPolynomial σ K)
  have hQ : Q = Q.comap E.toRingHom := by simp [E]
  have hψ' : (I.map E.toRingHom).map ψ.toRingHom ≤
      (J.map (algebraMap _ (Localization.Away p0))).map d.toRingHom := by
    simpa only [E, RingEquiv.toRingHom_refl', Ideal.map_id, hJ] using hψ
  have hd' : d.toRingHom.comp (rationalPolynomialChartMap p0 p).toRingHom =
      ψ.toRingHom.comp E.toRingHom := by simpa [E] using hd
  have hu := generalPointLocalQuotientPullback_unramified_coordinates I Q
    (J.map (algebraMap _ (Localization.Away p0))) P Q P' E d.toRingEquiv
    hQ hP (rationalPolynomialChartMap p0 p).toRingHom ψ.toRingHom hQP hQP' hφ hψ' hd' h
  refine ⟨hQP', hψ, ?_⟩
  have hId : I.map E.toRingHom = I := by simp [E]
  have hJd : (J.map (algebraMap _ (Localization.Away p0))).map
      d.toRingEquiv.toRingHom = J' := hJ
  have htransport (I' : Ideal (MvPolynomial σ K))
      (J'' : Ideal (Localization.Away (e p0)))
      (hI' : I.map E.toRingHom = I')
      (hJ' : (J.map (algebraMap _ (Localization.Away p0))).map
        d.toRingEquiv.toRingHom = J'')
      (hIJ : I'.map ψ.toRingHom ≤ J'') :
      (generalPointLocalQuotientPullback I' J'' P' Q ψ.toRingHom hQP' hIJ).FormallyUnramified := by
    subst I'
    subst J''
    exact hu
  exact htransport I J' hId hJd hψ

end LinearStudy
