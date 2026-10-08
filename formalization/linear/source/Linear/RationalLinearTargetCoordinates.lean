module
public import Linear.PolynomialLinearGrading
public import Linear.HomogeneousRationalPullback
public import Linear.PointLocalPullbackCoordinateComparison
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open scoped Matrix

/-- Linear target coordinates act on the ORIGINAL numerators. The actual
denominator is unchanged; the rational map is the original pullback composed
with this linear coordinate map. -/
theorem rationalPolynomialChartMap_target_linear_coordinates
    {K σ : Type*} [Field K] [Fintype σ]
    (M : Matrix σ σ K) (p0 : MvPolynomial σ K)
    (p : σ → MvPolynomial σ K) :
    rationalPolynomialChartMap p0 (fun i => MvPolynomial.aeval p (M.toMvPolynomial i)) =
      (rationalPolynomialChartMap p0 p).comp (polynomialLinearChange M) := by
  classical
  let v : σ → Localization.Away p0 := fun j => algebraMap _ _ (p j)
  have he : (IsScalarTower.toAlgHom K (MvPolynomial σ K) (Localization.Away p0)).comp
      (MvPolynomial.aeval p) = MvPolynomial.aeval v := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [v]
  have hev (F : MvPolynomial σ K) : MvPolynomial.aeval v F =
      algebraMap _ (Localization.Away p0) (MvPolynomial.aeval p F) :=
    (AlgHom.congr_fun he F).symm
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, rationalPolynomialChartMap, MvPolynomial.aeval_X]
  change algebraMap _ (Localization.Away p0)
      (MvPolynomial.aeval p (M.toMvPolynomial i)) * IsLocalization.Away.invSelf p0 =
    rationalPolynomialChartMap p0 p (polynomialLinearChange M (MvPolynomial.X i))
  have hX : polynomialLinearChange M (MvPolynomial.X i) = M.toMvPolynomial i := by
    simp [polynomialLinearChange]
  rw [hX]
  change _ = MvPolynomial.aeval (fun j => v j * IsLocalization.Away.invSelf p0) _
  have hv : (fun j => v j * IsLocalization.Away.invSelf p0) =
      (fun j => IsLocalization.Away.invSelf p0 * v j) := by
    funext j
    exact mul_comm _ _
  rw [hv, homogeneous_aeval_smul (Matrix.toMvPolynomial_isHomogeneous M i), pow_one, hev]
  exact mul_comm _ _

/-- Actual affine centering of the target is implemented by adding the
same denominator times the translation constant to each original numerator. -/
theorem rationalPolynomialChartMap_target_translation
    {K σ : Type*} [Field K]
    (a : σ → K) (p0 : MvPolynomial σ K) (p : σ → MvPolynomial σ K) :
    rationalPolynomialChartMap p0 (fun i => p i + MvPolynomial.C (a i) * p0) =
      (rationalPolynomialChartMap p0 p).comp (polynomialTranslation a).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  change rationalPolynomialChartMap p0 (fun i => p i + MvPolynomial.C (a i) * p0)
      (MvPolynomial.X i) = rationalPolynomialChartMap p0 p
        (polynomialTranslation a (MvPolynomial.X i))
  rw [polynomialTranslation_X]
  simp only [rationalPolynomialChartMap, MvPolynomial.aeval_X, map_add, map_mul,
    MvPolynomial.aeval_C]
  change (algebraMap (MvPolynomial σ K) (Localization.Away p0) (p i) +
      algebraMap (MvPolynomial σ K) (Localization.Away p0) (MvPolynomial.C (a i)) *
        algebraMap (MvPolynomial σ K) (Localization.Away p0) p0) * IsLocalization.Away.invSelf p0 =
    algebraMap (MvPolynomial σ K) (Localization.Away p0) (p i) * IsLocalization.Away.invSelf p0 +
      algebraMap K (Localization.Away p0) (a i)
  rw [add_mul, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
  congr 1

/-- Actual invertible target coordinates preserve the original local
quotient pullback's unramification. The transformed numerators, prime and
ideal compatibility are constructed from the original map. -/
theorem rationalPolynomialChartMap_unramified_target_linear_coordinates
    {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]
    (M : Matrix σ σ K) (hM : Matrix.det M ≠ 0)
    (p0 : MvPolynomial σ K) (p : σ → MvPolynomial σ K)
    (I Q : Ideal (MvPolynomial σ K)) [Q.IsPrime]
    (J P : Ideal (Localization.Away p0)) [P.IsPrime]
    (hQP : Q = P.comap (rationalPolynomialChartMap p0 p).toRingHom)
    (hφ : I.map (rationalPolynomialChartMap p0 p).toRingHom ≤ J)
    (h : (generalPointLocalQuotientPullback I J P Q
      (rationalPolynomialChartMap p0 p).toRingHom hQP hφ).FormallyUnramified) :
    let E := polynomialLinearChangeEquiv M hM
    let Q' := Q.comap E.symm.toRingHom
    letI : Q'.IsPrime := inferInstance
    let ψ := rationalPolynomialChartMap p0
      (fun i => MvPolynomial.aeval p ((M⁻¹).toMvPolynomial i))
    ∃ (hQP' : Q' = P.comap ψ.toRingHom) (hψ : (I.map E.toRingHom).map ψ.toRingHom ≤ J),
      (generalPointLocalQuotientPullback (I.map E.toRingHom) J P Q'
        ψ.toRingHom hQP' hψ).FormallyUnramified := by
  intro E Q'
  letI : Q'.IsPrime := inferInstance
  intro ψ
  have hψeq : ψ = (rationalPolynomialChartMap p0 p).comp E.symm.toAlgHom :=
    rationalPolynomialChartMap_target_linear_coordinates M⁻¹ p0 p
  have hsquare : ψ.comp E.toAlgHom = rationalPolynomialChartMap p0 p := by
    rw [hψeq]
    apply DFunLike.ext
    intro F
    change rationalPolynomialChartMap p0 p (E.symm (E F)) = rationalPolynomialChartMap p0 p F
    rw [E.symm_apply_apply]
  have hsquareR : ψ.toRingHom.comp E.toRingHom =
      (rationalPolynomialChartMap p0 p).toRingHom := by
    apply RingHom.ext
    intro F
    exact AlgHom.congr_fun hsquare F
  have hQ : Q = Q'.comap E.toRingHom := by
    ext F
    change F ∈ Q ↔ E.symm (E F) ∈ Q
    rw [E.symm_apply_apply]
  have hQP' : Q' = P.comap ψ.toRingHom := by
    change Q.comap E.symm.toRingHom = _
    rw [hQP, Ideal.comap_comap]
    exact congrArg (fun f => P.comap f) (congrArg AlgHom.toRingHom hψeq).symm
  have hψ : (I.map E.toRingHom).map ψ.toRingHom ≤ J := by
    rw [Ideal.map_map, hsquareR]
    exact hφ
  let D := RingEquiv.refl (Localization.Away p0)
  have hP : P = P.comap D.toRingHom := by simp [D]
  have hd : D.toRingHom.comp (rationalPolynomialChartMap p0 p).toRingHom =
      ψ.toRingHom.comp E.toRingHom := by
    change (rationalPolynomialChartMap p0 p).toRingHom = ψ.toRingHom.comp E.toRingHom
    exact hsquareR.symm
  have hψ' : (I.map E.toRingHom).map ψ.toRingHom ≤ J.map D.toRingHom := by
    simpa [D] using hψ
  have hu := generalPointLocalQuotientPullback_unramified_coordinates I Q J P Q' P
    E.toRingEquiv D hQ hP (rationalPolynomialChartMap p0 p).toRingHom
    ψ.toRingHom hQP hQP' hφ hψ' hd h
  refine ⟨hQP', hψ, ?_⟩
  have hId : J.map D.toRingHom = J := by simp [D]
  have htransport (J' : Ideal (Localization.Away p0)) (hJ' : J.map D.toRingHom = J')
      (hIJ : (I.map E.toRingHom).map ψ.toRingHom ≤ J') :
      (generalPointLocalQuotientPullback (I.map E.toRingHom) J' P Q'
        ψ.toRingHom hQP' hIJ).FormallyUnramified := by
    subst J'
    exact hu
  exact htransport J hId hψ

end LinearStudy
