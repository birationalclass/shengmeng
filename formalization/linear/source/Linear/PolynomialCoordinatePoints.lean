module
public import Linear.PolynomialAwayCoordinateEquiv
public import Linear.LocalGeneratorsEquiv
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy

/-- Every actual polynomial coordinate equivalence constructs the new point;
the evaluation comparison is derived, not assumed. -/
theorem polynomial_coordinate_point_evaluation
    {K σ τ : Type*} [Field K]
    (E : MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K) (x : σ → K) :
    let y := fun j => MvPolynomial.eval x (E.symm (MvPolynomial.X j))
    (MvPolynomial.aeval (R := K) y).comp E.toAlgHom = MvPolynomial.aeval x := by
  intro y
  have h : (MvPolynomial.aeval (R := K) x).comp E.symm.toAlgHom = MvPolynomial.aeval y := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    rfl
  rw [← h]
  apply DFunLike.ext
  intro F
  change MvPolynomial.eval x (E.symm (E F)) = MvPolynomial.eval x F
  rw [E.symm_apply_apply]

theorem polynomial_coordinate_point_kernel
    {K σ τ : Type*} [Field K]
    (E : MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K) (x : σ → K) :
    let y := fun j => MvPolynomial.eval x (E.symm (MvPolynomial.X j))
    RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom =
      (RingHom.ker (MvPolynomial.aeval (R := K) y).toRingHom).comap E.toRingHom := by
  intro y
  rw [RingHom.comap_ker]
  exact congrArg (fun f : MvPolynomial σ K →ₐ[K] K => RingHom.ker f.toRingHom)
    (polynomial_coordinate_point_evaluation E x).symm

/-- The SAME actual nonzero denominator and actual point evaluation survive
source coordinates; in particular the transformed prime is the new point. -/
theorem polynomial_coordinate_away_point_evaluation
    {K σ τ : Type*} [Field K]
    (E : MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K) (x : σ → K)
    (p0 : MvPolynomial σ K) (hp0 : MvPolynomial.eval x p0 ≠ 0) :
    let y := fun j => MvPolynomial.eval x (E.symm (MvPolynomial.X j))
    ∃ hp0' : MvPolynomial.eval y (E p0) ≠ 0,
      (polynomialAwayPointEvaluation y (E p0) hp0').comp
        (polynomialAwayCoordinateEquiv E p0).toAlgHom =
          polynomialAwayPointEvaluation x p0 hp0 ∧
      (RingHom.ker (polynomialAwayPointEvaluation x p0 hp0).toRingHom).comap
        (polynomialAwayCoordinateEquiv E p0).symm.toRingHom =
          RingHom.ker (polynomialAwayPointEvaluation y (E p0) hp0').toRingHom := by
  intro y
  have he (F : MvPolynomial σ K) : MvPolynomial.eval y (E F) = MvPolynomial.eval x F :=
    AlgHom.congr_fun (polynomial_coordinate_point_evaluation E x) F
  have hp0' : MvPolynomial.eval y (E p0) ≠ 0 := by
    rw [he]
    exact hp0
  let d := polynomialAwayCoordinateEquiv E p0
  have h : (polynomialAwayPointEvaluation y (E p0) hp0').comp d.toAlgHom =
      polynomialAwayPointEvaluation x p0 hp0 := by
    apply IsLocalization.algHom_ext (Submonoid.powers p0)
    apply DFunLike.ext
    intro F
    change polynomialAwayPointEvaluation y (E p0) hp0'
      (d (algebraMap _ (Localization.Away p0) F)) =
        polynomialAwayPointEvaluation x p0 hp0 (algebraMap _ (Localization.Away p0) F)
    rw [polynomialAwayCoordinateEquiv_algebraMap,
      polynomialAwayPointEvaluation_algebraMap, polynomialAwayPointEvaluation_algebraMap, he]
  refine ⟨hp0', h, ?_⟩
  have hk : RingHom.ker (polynomialAwayPointEvaluation x p0 hp0).toRingHom =
      (RingHom.ker (polynomialAwayPointEvaluation y (E p0) hp0').toRingHom).comap d.toRingHom := by
    rw [RingHom.comap_ker]
    exact congrArg (fun f : Localization.Away p0 →ₐ[K] K => RingHom.ker f.toRingHom) h.symm
  rw [hk, Ideal.comap_comap]
  ext a
  change polynomialAwayPointEvaluation y (E p0) hp0' (d (d.symm a)) = 0 ↔
    polynomialAwayPointEvaluation y (E p0) hp0' a = 0
  rw [d.apply_symm_apply]

theorem polynomial_coordinate_local_generators
    {K σ τ ι : Type*} [Field K]
    (E : MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K) (x : σ → K)
    (I : Ideal (MvPolynomial σ K)) (G : ι → MvPolynomial σ K)
    (hs : let P := RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom
      letI : P.IsPrime := RingHom.ker_isPrime _
      I.map (algebraMap _ (Localization.AtPrime P)) =
        Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i)))) :
    let y := fun j => MvPolynomial.eval x (E.symm (MvPolynomial.X j))
    let Q := RingHom.ker (MvPolynomial.aeval (R := K) y).toRingHom
    letI : Q.IsPrime := RingHom.ker_isPrime _
    (I.map E.toRingHom).map (algebraMap _ (Localization.AtPrime Q)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime Q) (E (G i)))) := by
  intro y Q
  letI : Q.IsPrime := RingHom.ker_isPrime _
  letI : (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom).IsPrime := RingHom.ker_isPrime _
  exact local_ideal_generators_under_ringEquiv I _ Q E.toRingEquiv
    (polynomial_coordinate_point_kernel E x) G hs

end LinearStudy
