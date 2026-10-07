module
public import Linear.RationalUnramifiedParameters
public import Linear.SmoothTargetParameters
public import Linear.LocalQuotientMaximalIdeal
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace LinearStudy
variable {K : Type*} [Field K] {r c : ℕ} [Nonempty (Fin r)] [Nonempty (Fin c)]

/-- Smoothness constructs the target polynomials; the genuine unramified
ratio-chart local map then constructs the source formal parameters. -/
theorem rational_smooth_target_constructs_actual_formal_parameters
    (x : Fin r ⊕ Fin c → K) (p0 : MvPolynomial (Fin r ⊕ Fin c) K)
    (hp0 : MvPolynomial.eval x p0 ≠ 0) (p : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (I J : Ideal (MvPolynomial (Fin r ⊕ Fin c) K)) [I.IsPrime] (hI : I ≠ ⊥)
    (P : Ideal (Localization.Away p0)) [P.IsPrime]
    (p' : Ideal (MvPolynomial (Fin r ⊕ Fin c) K ⧸ I)) [p'.IsPrime] [Algebra.IsSmoothAt K p']
    (hp : (p'.comap (Ideal.Quotient.mk I)) = RingHom.ker (MvPolynomial.aeval (R := K)
      (fun i => MvPolynomial.eval x (p i) / MvPolynomial.eval x p0)).toRingHom)
    (hr : r = Module.finrank (MvPolynomial (Fin r ⊕ Fin c) K ⧸ I) (KaehlerDifferential K (MvPolynomial (Fin r ⊕ Fin c) K ⧸ I)))
    (hP : P = RingHom.ker (polynomialAwayPointEvaluation x p0 hp0).toRingHom)
    (hQP : (p'.comap (Ideal.Quotient.mk I)) = P.comap (rationalPolynomialChartMap p0 p).toRingHom)
    (hφ : I.map (rationalPolynomialChartMap p0 p).toRingHom ≤ (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))))
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hlocal : J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.AtPrime
      (P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))))) =
      Ideal.span (Set.range (fun i => algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.AtPrime
        (P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0)))) (G i))))
    (hfinite : letI := (generalPointLocalQuotientPullback I (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))) P (p'.comap (Ideal.Quotient.mk I)) (rationalPolynomialChartMap p0 p).toRingHom hQP hφ).toAlgebra
      Algebra.EssFiniteType (Localization.AtPrime (p'.comap (Ideal.Quotient.mk I)) ⧸ I.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.AtPrime (p'.comap (Ideal.Quotient.mk I))))) (Localization.AtPrime P ⧸ (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))).map (algebraMap (Localization.Away p0) (Localization.AtPrime P))))
    (hunram : letI := (generalPointLocalQuotientPullback I (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))) P (p'.comap (Ideal.Quotient.mk I)) (rationalPolynomialChartMap p0 p).toRingHom hQP hφ).toAlgebra
      Algebra.FormallyUnramified (Localization.AtPrime (p'.comap (Ideal.Quotient.mk I)) ⧸ I.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.AtPrime (p'.comap (Ideal.Quotient.mk I))))) (Localization.AtPrime P ⧸ (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))).map (algebraMap (Localization.Away p0) (Localization.AtPrime P))))
 :
    ∃ a : Fin r → MvPolynomial (Fin r ⊕ Fin c) K,
      let T := fun i => polynomialAwaySmoothReducedMap x p0 hp0 G hG hJ
        (rationalPolynomialChartMap p0 p (a i))
      Ideal.span (Set.range T) = IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K) ∧
        IsUnit (Matrix.det (fun i j => (MvPowerSeries.pderiv j (T i)).constantCoeff)) := by
  let Q := p'.comap (Ideal.Quotient.mk I)
  letI : Q.IsPrime := inferInstance
  have hIQ : I ≤ Q := by
    intro b hb
    change Ideal.Quotient.mk I b ∈ p'
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hb]
    exact p'.zero_mem
  let L := I.map (algebraMap _ (Localization.AtPrime Q))
  letI : Nontrivial (Localization.AtPrime Q ⧸ L) := Ideal.Quotient.nontrivial_iff.mpr
    (polynomial_local_ideal_ne_top I Q hIQ)
  letI : IsLocalRing (Localization.AtPrime Q ⧸ L) := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk L) Ideal.Quotient.mk_surjective
  obtain ⟨s, a, hs, ha⟩ := smoothLocus_constructs_original_polynomial_parameters
    I hI p' (fun i => MvPolynomial.eval x (p i) / MvPolynomial.eval x p0) hp
  have hsr : s = r := hs.trans hr.symm
  clear hs
  subst s
  have ha' : Ideal.span (Set.range (fun i => Ideal.Quotient.mk L
      (algebraMap _ (Localization.AtPrime Q) (a i)))) =
      (Q.map (algebraMap _ (Localization.AtPrime Q))).map (Ideal.Quotient.mk L) :=
    ha.trans (point_local_quotient_maximalIdeal_map I Q).symm
  exact ⟨a, rational_unramified_actual_formal_parameters x p0 hp0 p I J P Q
    hP hQP hφ G hG hJ hlocal hfinite hunram a ha'⟩

end LinearStudy
