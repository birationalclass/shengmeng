module
public import Linear.PolynomialCoordinatePoints
public import Linear.LocalizedPointQuotientEquiv
public import Mathlib.RingTheory.Ideal.Quotient.Operations
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open scoped Matrix

theorem linear_reindexed_actual_source_point
    {K σ τ : Type*} [Field K] [Fintype σ] [DecidableEq σ]
    (M : Matrix σ σ K) (hM : Matrix.det M ≠ 0) (e : τ ≃ σ) (x : σ → K) :
    let E := (polynomialLinearChangeEquiv M hM).trans (MvPolynomial.renameEquiv K e.symm)
    (fun j => MvPolynomial.eval x (E.symm (MvPolynomial.X j))) = (M⁻¹ *ᵥ x) ∘ e := by
  intro E
  funext j
  dsimp only [E]
  rw [AlgEquiv.symm_trans_apply, MvPolynomial.renameEquiv_symm]
  simp only [Equiv.symm_symm, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  change MvPolynomial.eval x (polynomialLinearChange M⁻¹ (MvPolynomial.X (e j))) = _
  rw [eval_polynomialLinearChange]
  simp

/-- Actual source generators are transported to the point prime used in the
localized rational map, rather than an independently supplied formal prime. -/
theorem polynomial_coordinate_away_local_generators
    {K σ τ ι : Type*} [Field K]
    (E : MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K) (x : σ → K)
    (I : Ideal (MvPolynomial σ K)) (G : ι → MvPolynomial σ K)
    (hs : let P := RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom
      letI : P.IsPrime := RingHom.ker_isPrime _
      I.map (algebraMap _ (Localization.AtPrime P)) =
        Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i))))
    (p0 : MvPolynomial τ K)
    (hp0 : MvPolynomial.eval (fun j => MvPolynomial.eval x (E.symm (MvPolynomial.X j))) p0 ≠ 0) :
    let y := fun j => MvPolynomial.eval x (E.symm (MvPolynomial.X j))
    let P := RingHom.ker (polynomialAwayPointEvaluation y p0 hp0).toRingHom
    letI : P.IsPrime := RingHom.ker_isPrime _
    (I.map E.toRingHom).map (algebraMap _ (Localization.AtPrime
      (P.comap (algebraMap (MvPolynomial τ K) (Localization.Away p0))))) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime
        (P.comap (algebraMap (MvPolynomial τ K) (Localization.Away p0)))) (E (G i)))) := by
  intro y P
  letI : P.IsPrime := RingHom.ker_isPrime _
  letI : (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom).IsPrime := RingHom.ker_isPrime _
  have hP : RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom =
      (P.comap (algebraMap (MvPolynomial τ K) (Localization.Away p0))).comap E.toRingHom := by
    rw [polynomialAwayPointEvaluation_point_comap]
    exact polynomial_coordinate_point_kernel E x
  exact local_ideal_generators_under_ringEquiv I _ _ E.toRingEquiv hP G hs

/-- The actual target-origin prime comparison forces every centered numerator
to vanish at the actual source point; this is not a separate fiber input. -/
theorem rational_target_origin_numerators_vanish
    {K σ : Type*} [Field K]
    (x : σ → K) (p0 : MvPolynomial σ K) (hp0 : MvPolynomial.eval x p0 ≠ 0)
    (p : σ → MvPolynomial σ K)
    (hQP : RingHom.ker (MvPolynomial.aeval (R := K) (0 : σ → K)).toRingHom =
      (RingHom.ker (polynomialAwayPointEvaluation x p0 hp0).toRingHom).comap
        (rationalPolynomialChartMap p0 p).toRingHom) :
    ∀ i, MvPolynomial.eval x (p i) = 0 := by
  intro i
  have hmem : MvPolynomial.X i ∈ RingHom.ker
      (MvPolynomial.aeval (R := K) (0 : σ → K)).toRingHom := by simp
  rw [hQP] at hmem
  have hzero : ((polynomialAwayPointEvaluation x p0 hp0).comp
      (rationalPolynomialChartMap p0 p)) (MvPolynomial.X i) = 0 := hmem
  rw [rationalPolynomialChartMap_point_evaluation] at hzero
  simp only [MvPolynomial.aeval_X] at hzero
  exact (div_eq_zero_iff).mp hzero |>.resolve_right hp0

/-- Construct the actual evaluation of the full equation quotient from the
derived numerator vanishing, with its exact original point coordinates. -/
theorem polynomial_equation_quotient_actual_point
    {K σ : Type*} [Field K] (x : σ → K) (p : σ → MvPolynomial σ K)
    (hp : ∀ i, MvPolynomial.eval x (p i) = 0) :
    ∃ q : (MvPolynomial σ K ⧸ Ideal.span (Set.range p)) →ₐ[K] K,
      x = fun i => q (Ideal.Quotient.mk (Ideal.span (Set.range p)) (MvPolynomial.X i)) := by
  have hI : Ideal.span (Set.range p) ≤ RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hp i
  refine ⟨Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (R := K) x) hI, ?_⟩
  funext i
  simp

end LinearStudy
