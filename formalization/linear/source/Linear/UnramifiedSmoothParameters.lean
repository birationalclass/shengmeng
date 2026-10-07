module
public import Linear.PolynomialSmoothReduction
public import Linear.UnramifiedParameters
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace LinearStudy
variable {K : Type*} [Field K] {r c : ℕ} [Nonempty (Fin c)] [Nonempty (Fin r)]

theorem smooth_local_unramified_parameters_generate
    (I P : Ideal (MvPolynomial (Fin r ⊕ Fin c) K)) [P.IsPrime]
    (x : Fin r ⊕ Fin c → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hlocal : I.map (algebraMap _ (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i))))
    (R : Type*) [CommRing R] [IsLocalRing R]
    [Algebra R (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))]
    [IsLocalHom (algebraMap R (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))))]
    [Algebra.EssFiniteType R (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))]
    [Algebra.FormallyUnramified R (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))]
    (t : Fin r → R) (ht : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal R) :
    let S := Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))
    let φ := polynomialSmoothLocalQuotientReduction I P x hP G hG hJ hlocal
    let T := fun i => φ (algebraMap R S (t i))
    Ideal.span (Set.range T) = IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K) ∧
      IsUnit (Matrix.det (fun i j => (MvPowerSeries.pderiv j (T i)).constantCoeff)) := by
  let S := Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))
  let : IsLocalRing S := polynomialSmoothLocalQuotient_isLocalRing I P x hP G hG hJ hlocal
  let φ := polynomialSmoothLocalQuotientReduction I P x hP G hG hJ hlocal
  let T := fun i => φ (algebraMap R S (t i))
  have h := congrArg (fun J : Ideal S => J.map φ) (unramified_local_parameters_generate (S := S) t ht)
  rw [Ideal.map_span, ← Set.range_comp] at h
  have hφ : (IsLocalRing.maximalIdeal S).map φ = IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K) :=
    local_quotient_reduction_maximalIdeal _ _
      (polynomialSmoothPointLocalReduction_ideal_kernel I P x hP G hG hJ hlocal)
      (polynomialSmoothPointLocalReduction_maximalIdeal P x hP G hG hJ)
  have hT : Ideal.span (Set.range T) = IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K) :=
    h.trans hφ
  exact ⟨hT, parameter_generators_jacobian_constantCoeff_unit T hT⟩

end LinearStudy
