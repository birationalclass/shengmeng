module
public import Linear.LocalQuotientPullback
public import Linear.UnramifiedParameters
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace LinearStudy

theorem point_local_unramified_parameters_generate {R ι : Type*} [CommRing R]
    (I P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    [IsLocalRing (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P)))]
    (φ : R →+* R) (hQP : Q = P.comap φ) (hφ : I.map φ ≤ I)
    (hfinite : letI := (pointLocalQuotientPullback I P Q φ hQP hφ).toAlgebra
      Algebra.EssFiniteType
        (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q)))
        (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P))))
    (hunram : letI := (pointLocalQuotientPullback I P Q φ hQP hφ).toAlgebra
      Algebra.FormallyUnramified
        (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q)))
        (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P))))
    (t : ι → (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))))
    (ht : Ideal.span (Set.range t) =
      (Q.map (algebraMap R (Localization.AtPrime Q))).map (Ideal.Quotient.mk _)) :
    Ideal.span (Set.range (fun i => pointLocalQuotientPullback I P Q φ hQP hφ (t i))) =
      IsLocalRing.maximalIdeal
        (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P))) := by
  let A := Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))
  let B := Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P))
  let Φ := pointLocalQuotientPullback I P Q φ hQP hφ
  let : IsLocalHom Φ := pointLocalQuotientPullback_isLocalHom I P Q φ hQP hφ
  let : IsLocalRing A := Φ.domain_isLocalRing
  let : Algebra A B := Φ.toAlgebra
  let : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom Φ)
  let : Algebra.EssFiniteType A B := hfinite
  let : Algebra.FormallyUnramified A B := hunram
  have hgen : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A := by
    rw [ht, Localization.AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  exact unramified_local_parameters_generate (S := B) t hgen

theorem smooth_actual_unramified_pullback_parameters {K : Type*} [Field K]
    {r c : ℕ} [Nonempty (Fin c)] [Nonempty (Fin r)]
    (I P Q : Ideal (MvPolynomial (Fin r ⊕ Fin c) K)) [P.IsPrime] [Q.IsPrime]
    (x : Fin r ⊕ Fin c → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (F : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hQP : Q = P.comap (MvPolynomial.aeval F).toRingHom)
    (hF : I.map (MvPolynomial.aeval F).toRingHom ≤ I)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hlocal : I.map (algebraMap _ (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i))))
    (hfinite : letI := (pointLocalQuotientPullback I P Q (MvPolynomial.aeval F).toRingHom hQP hF).toAlgebra
      Algebra.EssFiniteType
        (Localization.AtPrime Q ⧸ I.map (algebraMap _ (Localization.AtPrime Q)))
        (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))))
    (hunram : letI := (pointLocalQuotientPullback I P Q (MvPolynomial.aeval F).toRingHom hQP hF).toAlgebra
      Algebra.FormallyUnramified
        (Localization.AtPrime Q ⧸ I.map (algebraMap _ (Localization.AtPrime Q)))
        (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))))
    (a : Fin r → MvPolynomial (Fin r ⊕ Fin c) K)
    (ha : Ideal.span (Set.range (fun i => Ideal.Quotient.mk _
      (algebraMap _ (Localization.AtPrime Q) (a i)))) =
      (Q.map (algebraMap _ (Localization.AtPrime Q))).map
        (Ideal.Quotient.mk (I.map (algebraMap _ (Localization.AtPrime Q))))) :
    let T := fun i => polynomialSmoothReducedMap x G hG hJ (MvPolynomial.aeval F (a i))
    Ideal.span (Set.range T) = IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K) ∧
      IsUnit (Matrix.det (fun i j => (MvPowerSeries.pderiv j (T i)).constantCoeff)) := by
  let S := Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))
  let : IsLocalRing S := polynomialSmoothLocalQuotient_isLocalRing I P x hP G hG hJ hlocal
  let χ := polynomialSmoothLocalQuotientReduction I P x hP G hG hJ hlocal
  have hs := point_local_unramified_parameters_generate I P Q
    (MvPolynomial.aeval F).toRingHom hQP hF hfinite hunram _ ha
  have hh := congrArg (fun J : Ideal S => J.map χ) hs
  rw [Ideal.map_span, ← Set.range_comp] at hh
  have hχ : (IsLocalRing.maximalIdeal S).map χ =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K) :=
    local_quotient_reduction_maximalIdeal _ _
      (polynomialSmoothPointLocalReduction_ideal_kernel I P x hP G hG hJ hlocal)
      (polynomialSmoothPointLocalReduction_maximalIdeal P x hP G hG hJ)
  rw [hχ] at hh
  have he : (χ ∘ fun i => pointLocalQuotientPullback I P Q
      (MvPolynomial.aeval F).toRingHom hQP hF
        (Ideal.Quotient.mk _ (algebraMap _ (Localization.AtPrime Q) (a i)))) =
      (fun i => polynomialSmoothReducedMap x G hG hJ (MvPolynomial.aeval F (a i))) := by
    funext i
    exact smooth_local_quotient_pullback_reduction I P Q x hP F hQP hF G hG hJ hlocal (a i)
  rw [he] at hh
  exact ⟨hh, parameter_generators_jacobian_constantCoeff_unit _ hh⟩

end LinearStudy
