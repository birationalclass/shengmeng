module
public import Linear.RationalReindexedSourceCoordinates
public import Linear.RationalTargetCenterUnramified
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy
open scoped Matrix

/-- Derive the SAME local quotient map after independent source coordinates,
target reindexing, linear normalization and centering. All intermediate
primes and containments are constructed from the original actual map. -/
theorem rational_reindexed_centered_actual_local_map
    {K σ τ : Type*} [Field K] [Fintype τ] [DecidableEq τ]
    (E : MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K) (b : σ ≃ τ)
    (M : Matrix τ τ K) (hM : Matrix.det M ≠ 0) (z : τ → K)
    (p0 : MvPolynomial σ K) (p : σ → MvPolynomial σ K)
    (I J Q : Ideal (MvPolynomial σ K)) [Q.IsPrime]
    (P : Ideal (Localization.Away p0)) [P.IsPrime]
    (hQP : Q = P.comap (rationalPolynomialChartMap p0 p).toRingHom)
    (hφ : I.map (rationalPolynomialChartMap p0 p).toRingHom ≤
      J.map (algebraMap _ (Localization.Away p0)))
    (h : (generalPointLocalQuotientPullback I
      (J.map (algebraMap _ (Localization.Away p0))) P Q
        (rationalPolynomialChartMap p0 p).toRingHom hQP hφ).FormallyUnramified) :
    let E0 := MvPolynomial.renameEquiv K b
    let EL := polynomialLinearChangeEquiv M hM
    let EC := polynomialTranslation z
    let d := polynomialAwayCoordinateEquiv E p0
    let P' := P.comap d.symm.toRingHom
    let Q' := ((Q.comap E0.symm.toRingHom).comap EL.symm.toRingHom).comap EC.symm.toRingHom
    letI : P'.IsPrime := inferInstance
    letI : Q'.IsPrime := inferInstance
    let p' := fun j => E (p (b.symm j))
    let pL := fun i => MvPolynomial.aeval p' ((M⁻¹).toMvPolynomial i)
    let pC := fun i => pL i - MvPolynomial.C (z i) * E p0
    let ψ := rationalPolynomialChartMap (E p0) pC
    let I' := ((I.map E0.toRingHom).map EL.toRingHom).map EC.toRingHom
    let J' := (J.map E.toRingHom).map (algebraMap _ (Localization.Away (E p0)))
    ∃ (hQP' : Q' = P'.comap ψ.toRingHom) (hψ : I'.map ψ.toRingHom ≤ J'),
      (generalPointLocalQuotientPullback I' J' P' Q'
        ψ.toRingHom hQP' hψ).FormallyUnramified := by
  intro E0 EL EC d P' Q'
  letI : P'.IsPrime := inferInstance
  letI : Q'.IsPrime := inferInstance
  intro p' pL pC ψ I' J'
  let Q0 := Q.comap E0.symm.toRingHom
  let QL := Q0.comap EL.symm.toRingHom
  letI : Q0.IsPrime := inferInstance
  letI : QL.IsPrime := inferInstance
  obtain ⟨hQ0,hφ0,hu0⟩ := rational_source_coordinates_target_reindex_unramified
    E b p0 p I J Q P hQP hφ h
  obtain ⟨hQL,hφL,huL⟩ := rationalPolynomialChartMap_unramified_target_linear_coordinates
    M hM (E p0) p' (I.map E0.toRingHom) Q0 J' P' hQ0 hφ0 hu0
  exact rationalPolynomialChartMap_unramified_target_centering z (E p0) pL
    ((I.map E0.toRingHom).map EL.toRingHom) QL J' P' hQL hφL huL

end LinearStudy
