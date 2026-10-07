module
public import Linear.GeneralLocalQuotientPullback
public import Linear.UnramifiedParameters
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy

theorem general_point_local_unramified_parameters_generate {R A ι : Type*}
    [CommRing R] [CommRing A]
    (I : Ideal R) (J P : Ideal A) (Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    [IsLocalRing (Localization.AtPrime P ⧸ J.map (algebraMap A (Localization.AtPrime P)))]
    (φ : R →+* A) (hQP : Q = P.comap φ) (hφ : I.map φ ≤ J)
    (hfinite : letI := (generalPointLocalQuotientPullback I J P Q φ hQP hφ).toAlgebra
      Algebra.EssFiniteType
        (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q)))
        (Localization.AtPrime P ⧸ J.map (algebraMap A (Localization.AtPrime P))))
    (hunram : letI := (generalPointLocalQuotientPullback I J P Q φ hQP hφ).toAlgebra
      Algebra.FormallyUnramified
        (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q)))
        (Localization.AtPrime P ⧸ J.map (algebraMap A (Localization.AtPrime P))))
    (t : ι → (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))))
    (ht : Ideal.span (Set.range t) =
      (Q.map (algebraMap R (Localization.AtPrime Q))).map (Ideal.Quotient.mk _)) :
    Ideal.span (Set.range (fun i => generalPointLocalQuotientPullback I J P Q φ hQP hφ (t i))) =
      IsLocalRing.maximalIdeal
        (Localization.AtPrime P ⧸ J.map (algebraMap A (Localization.AtPrime P))) := by
  let S := Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))
  let B := Localization.AtPrime P ⧸ J.map (algebraMap A (Localization.AtPrime P))
  let Φ := generalPointLocalQuotientPullback I J P Q φ hQP hφ
  letI : IsLocalHom Φ := generalPointLocalQuotientPullback_isLocalHom I J P Q φ hQP hφ
  letI : IsLocalRing S := Φ.domain_isLocalRing
  letI : Algebra S B := Φ.toAlgebra
  letI : IsLocalHom (algebraMap S B) := inferInstanceAs (IsLocalHom Φ)
  letI : Algebra.EssFiniteType S B := hfinite
  letI : Algebra.FormallyUnramified S B := hunram
  have hgen : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal S := by
    rw [ht, Localization.AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  exact unramified_local_parameters_generate (S := B) t hgen

end LinearStudy
