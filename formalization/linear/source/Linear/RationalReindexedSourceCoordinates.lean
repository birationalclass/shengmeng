module
public import Linear.RationalCoordinateSandwich
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy

/-- Source polynomial coordinates and target variable reindexing may be
chosen independently. The original numerator/denominator formulas construct
the actual rational map square across the ACTUAL source localization. -/
theorem rational_source_coordinates_target_reindex_square
    {K σ τ : Type*} [Field K]
    (e : MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K) (b : σ ≃ τ)
    (p0 : MvPolynomial σ K) (p : σ → MvPolynomial σ K) :
    (polynomialAwayCoordinateEquiv e p0).toAlgHom.comp (rationalPolynomialChartMap p0 p) =
      (rationalPolynomialChartMap (e p0) (fun j => e (p (b.symm j)))).comp
        (MvPolynomial.renameEquiv K b).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [rationalPolynomialChartMap, polynomialAwayCoordinateEquiv_algebraMap,
    polynomialAwayCoordinateEquiv_invSelf, MvPolynomial.renameEquiv_apply]

/-- Original ideal powers survive independent source coordinates and target
reindexing. All changed ideals and the actual localized map are constructed. -/
theorem rational_source_coordinates_target_reindex_power_sandwich
    {K σ τ : Type*} [Field K]
    (e : MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K) (b : σ ≃ τ)
    (p0 : MvPolynomial σ K) (p : σ → MvPolynomial σ K)
    (I J : Ideal (MvPolynomial σ K)) (m : ℕ)
    (hlo : (J.map (algebraMap _ (Localization.Away p0))) ^ m ≤
      I.map (rationalPolynomialChartMap p0 p).toRingHom)
    (hhi : I.map (rationalPolynomialChartMap p0 p).toRingHom ≤
      J.map (algebraMap _ (Localization.Away p0))) :
    ((J.map e.toRingHom).map (algebraMap _ (Localization.Away (e p0)))) ^ m ≤
      (I.map (MvPolynomial.renameEquiv K b).toRingHom).map
        (rationalPolynomialChartMap (e p0) (fun j => e (p (b.symm j)))).toRingHom ∧
    (I.map (MvPolynomial.renameEquiv K b).toRingHom).map
        (rationalPolynomialChartMap (e p0) (fun j => e (p (b.symm j)))).toRingHom ≤
      (J.map e.toRingHom).map (algebraMap _ (Localization.Away (e p0))) := by
  let d := polynomialAwayCoordinateEquiv e p0
  have hd := congrArg AlgHom.toRingHom
    (rational_source_coordinates_target_reindex_square e b p0 p)
  have h := ideal_power_sandwich_under_coordinate_diagram (MvPolynomial.renameEquiv K b).toRingEquiv
    d.toRingEquiv (rationalPolynomialChartMap p0 p).toRingHom
    (rationalPolynomialChartMap (e p0) (fun j => e (p (b.symm j)))).toRingHom
    hd I (J.map (algebraMap _ (Localization.Away p0))) m hlo hhi
  rw [polynomialAwayCoordinateEquiv_original_ideal] at h
  exact h

/-- The ORIGINAL unramified local map survives independent source
coordinates and target reindexing. Transformed primes, containment and the
local diagram are derived, not independent geometric assumptions. -/
theorem rational_source_coordinates_target_reindex_unramified
    {K σ τ : Type*} [Field K]
    (e : MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K) (b : σ ≃ τ)
    (p0 : MvPolynomial σ K) (p : σ → MvPolynomial σ K)
    (I J Q : Ideal (MvPolynomial σ K)) [Q.IsPrime]
    (P : Ideal (Localization.Away p0)) [P.IsPrime]
    (hQP : Q = P.comap (rationalPolynomialChartMap p0 p).toRingHom)
    (hφ : I.map (rationalPolynomialChartMap p0 p).toRingHom ≤
      J.map (algebraMap _ (Localization.Away p0)))
    (h : (generalPointLocalQuotientPullback I
      (J.map (algebraMap _ (Localization.Away p0))) P Q
        (rationalPolynomialChartMap p0 p).toRingHom hQP hφ).FormallyUnramified) :
    let E := MvPolynomial.renameEquiv K b
    let d := polynomialAwayCoordinateEquiv e p0
    let Q' := Q.comap E.symm.toRingHom
    let P' := P.comap d.symm.toRingHom
    letI : Q'.IsPrime := inferInstance
    letI : P'.IsPrime := inferInstance
    let ψ := rationalPolynomialChartMap (e p0) (fun j => e (p (b.symm j)))
    let I' := I.map E.toRingHom
    let J' := (J.map e.toRingHom).map (algebraMap _ (Localization.Away (e p0)))
    ∃ (hQP' : Q' = P'.comap ψ.toRingHom) (hψ : I'.map ψ.toRingHom ≤ J'),
      (generalPointLocalQuotientPullback I' J' P' Q'
        ψ.toRingHom hQP' hψ).FormallyUnramified := by
  intro E d Q' P'
  letI : Q'.IsPrime := inferInstance
  letI : P'.IsPrime := inferInstance
  intro ψ I' J'
  have hQ : Q = Q'.comap E.toRingHom := by
    ext F
    change F ∈ Q ↔ E.symm (E F) ∈ Q
    rw [AlgEquiv.symm_apply_apply]
  have hP : P = P'.comap d.toRingHom := by
    ext F
    change F ∈ P ↔ d.symm (d F) ∈ P
    rw [AlgEquiv.symm_apply_apply]
  have hd : d.toRingHom.comp (rationalPolynomialChartMap p0 p).toRingHom =
      ψ.toRingHom.comp E.toRingHom :=
    congrArg AlgHom.toRingHom (rational_source_coordinates_target_reindex_square e b p0 p)
  have hQP' : Q' = P'.comap ψ.toRingHom := by
    apply Ideal.comap_injective_of_surjective E.toRingHom E.surjective
    rw [← hQ, Ideal.comap_comap, ← hd, ← Ideal.comap_comap, ← hP]
    exact hQP
  have hJ : (J.map (algebraMap _ (Localization.Away p0))).map d.toRingHom = J' :=
    polynomialAwayCoordinateEquiv_original_ideal e p0 J
  have hψ : I'.map ψ.toRingHom ≤ J' := by
    have hh := Ideal.map_mono (f := d.toRingHom) hφ
    rw [Ideal.map_map, hd, ← Ideal.map_map, hJ] at hh
    exact hh
  have hψ' : (I.map E.toRingHom).map ψ.toRingHom ≤
      (J.map (algebraMap _ (Localization.Away p0))).map d.toRingHom := by
    rw [hJ]
    exact hψ
  have hu := generalPointLocalQuotientPullback_unramified_coordinates I Q
    (J.map (algebraMap _ (Localization.Away p0))) P Q' P' E.toRingEquiv d.toRingEquiv
    hQ hP (rationalPolynomialChartMap p0 p).toRingHom ψ.toRingHom hQP hQP'
    hφ hψ' hd h
  refine ⟨hQP',hψ,?_⟩
  have htransport (J'' : Ideal (Localization.Away (e p0)))
      (hJ' : (J.map (algebraMap _ (Localization.Away p0))).map d.toRingHom = J'')
      (hIJ : I'.map ψ.toRingHom ≤ J'') :
      (generalPointLocalQuotientPullback I' J'' P' Q'
        ψ.toRingHom hQP' hIJ).FormallyUnramified := by
    subst J''
    exact hu
  exact htransport J' hJ hψ

end LinearStudy
