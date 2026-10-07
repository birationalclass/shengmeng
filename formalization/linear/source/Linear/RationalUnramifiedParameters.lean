module
public import Linear.RationalSmoothReduction
public import Linear.GeneralUnramifiedPullback
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace LinearStudy
variable {K : Type*} [Field K] {r c : ℕ} [Nonempty (Fin r)] [Nonempty (Fin c)]

/-- The genuine localized rational chart, not a polynomial stand-in, transfers
actual unramified target parameters to constructed source formal coordinates. -/
theorem rational_unramified_actual_formal_parameters
    (x : Fin r ⊕ Fin c → K) (p0 : MvPolynomial (Fin r ⊕ Fin c) K)
    (hp0 : MvPolynomial.eval x p0 ≠ 0) (p : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (I J : Ideal (MvPolynomial (Fin r ⊕ Fin c) K)) (P : Ideal (Localization.Away p0)) (Q : Ideal (MvPolynomial (Fin r ⊕ Fin c) K)) [P.IsPrime] [Q.IsPrime]
    (hP : P = RingHom.ker (polynomialAwayPointEvaluation x p0 hp0).toRingHom)
    (hQP : Q = P.comap (rationalPolynomialChartMap p0 p).toRingHom)
    (hφ : I.map (rationalPolynomialChartMap p0 p).toRingHom ≤ (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))))
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hlocal : J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.AtPrime
      (P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))))) =
      Ideal.span (Set.range (fun i => algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.AtPrime
        (P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0)))) (G i))))
    (hfinite : letI := (generalPointLocalQuotientPullback I (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))) P Q (rationalPolynomialChartMap p0 p).toRingHom hQP hφ).toAlgebra
      Algebra.EssFiniteType (Localization.AtPrime Q ⧸ I.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.AtPrime Q))) (Localization.AtPrime P ⧸ (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))).map (algebraMap (Localization.Away p0) (Localization.AtPrime P))))
    (hunram : letI := (generalPointLocalQuotientPullback I (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))) P Q (rationalPolynomialChartMap p0 p).toRingHom hQP hφ).toAlgebra
      Algebra.FormallyUnramified (Localization.AtPrime Q ⧸ I.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.AtPrime Q))) (Localization.AtPrime P ⧸ (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))).map (algebraMap (Localization.Away p0) (Localization.AtPrime P))))
    (a : Fin r → MvPolynomial (Fin r ⊕ Fin c) K)
    (ha : Ideal.span (Set.range (fun i => Ideal.Quotient.mk _
      (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.AtPrime Q) (a i)))) =
      (Q.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.AtPrime Q))).map
        (Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.AtPrime Q))))) :
    let T := fun i => polynomialAwaySmoothReducedMap x p0 hp0 G hG hJ
      (rationalPolynomialChartMap p0 p (a i))
    Ideal.span (Set.range T) = IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K) ∧
      IsUnit (Matrix.det (fun i j => (MvPowerSeries.pderiv j (T i)).constantCoeff)) := by
  have hPc : P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0)) =
      RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom := by
    rw [hP]
    exact polynomialAwayPointEvaluation_point_comap x p0 hp0
  let B := (Localization.AtPrime P ⧸ (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))).map (algebraMap (Localization.Away p0) (Localization.AtPrime P)))
  letI : IsLocalRing B := localizedSmoothPointQuotient_isLocalRing x p0 J P hPc G hG hJ hlocal
  let χ := localizedSmoothPointQuotientReduction x p0 J P hPc G hG hJ hlocal
  have hs := general_point_local_unramified_parameters_generate I
    (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))) P Q (rationalPolynomialChartMap p0 p).toRingHom hQP hφ hfinite hunram _ ha
  have hh := congrArg (fun L : Ideal B => L.map χ) hs
  rw [Ideal.map_span, ← Set.range_comp] at hh
  have hχ : (IsLocalRing.maximalIdeal B).map χ =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K) :=
    localizedSmoothPointQuotientReduction_maximalIdeal x p0 J P hPc G hG hJ hlocal
  rw [hχ] at hh
  have hcomp : χ.comp ((Ideal.Quotient.mk _).comp
      (algebraMap (Localization.Away p0) (Localization.AtPrime P))) =
        polynomialAwaySmoothReducedMap x p0 hp0 G hG hJ :=
    localizedSmoothPointQuotientReduction_away_comparison x p0 J P hPc G hG hJ hlocal hp0
  have he : (χ ∘ fun i => (generalPointLocalQuotientPullback I (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))) P Q (rationalPolynomialChartMap p0 p).toRingHom hQP hφ)
      (Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K)
        (Localization.AtPrime Q) (a i)))) =
      (fun i => polynomialAwaySmoothReducedMap x p0 hp0 G hG hJ
        (rationalPolynomialChartMap p0 p (a i))) := by
    funext i
    rw [Function.comp_apply, generalPointLocalQuotientPullback_mk]
    exact congrArg (fun f => f (rationalPolynomialChartMap p0 p (a i))) hcomp
  rw [he] at hh
  exact ⟨hh, parameter_generators_jacobian_constantCoeff_unit _ hh⟩

end LinearStudy
