module
public import Linear.ActualUnramifiedPullback
public import Linear.PolynomialLocalParameters
public import Linear.LocalQuotientMaximalIdeal
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 1600000
namespace LinearStudy

/-- Supply actual target equations, rather than assume the target parameter
span. The unramified pullback then generates the source formal maximal ideal. -/
theorem actual_target_normal_equations_unramified_pullback_parameters
    {K : Type*} [Field K] {r c : ℕ} [Nonempty (Fin r)] [Nonempty (Fin c)]
    (I P Q : Ideal (MvPolynomial (Fin r ⊕ Fin c) K)) [P.IsPrime] [Q.IsPrime]
    (x y : Fin r ⊕ Fin c → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (hQ : Q = RingHom.ker (MvPolynomial.aeval (R := K) y).toRingHom)
    (hIQ : I ≤ Q)
    (F : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hQP : Q = P.comap (MvPolynomial.aeval F).toRingHom)
    (hF : I.map (MvPolynomial.aeval F).toRingHom ≤ I)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hlocal : I.map (algebraMap _ (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i))))
    (H : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (htarget : I.map (algebraMap _ (Localization.AtPrime Q)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime Q) (H i))))
    (h0H : ∀ i, MvPolynomial.eval y (H i) = 0)
    (hDH : ∀ i j, MvPolynomial.eval y (MvPolynomial.pderiv j (H i)) =
      if j = Sum.inr i then 1 else 0)
    (hfinite : letI := (pointLocalQuotientPullback I P Q (MvPolynomial.aeval F).toRingHom hQP hF).toAlgebra
      Algebra.EssFiniteType
        (Localization.AtPrime Q ⧸ I.map (algebraMap _ (Localization.AtPrime Q)))
        (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))))
    (hunram : letI := (pointLocalQuotientPullback I P Q (MvPolynomial.aeval F).toRingHom hQP hF).toAlgebra
      Algebra.FormallyUnramified
        (Localization.AtPrime Q ⧸ I.map (algebraMap _ (Localization.AtPrime Q)))
        (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))) :
    let a : Fin r → MvPolynomial (Fin r ⊕ Fin c) K :=
      fun i => MvPolynomial.X (Sum.inl i) - MvPolynomial.C (y (Sum.inl i))
    let T := fun i => polynomialSmoothReducedMap x G hG hJ (MvPolynomial.aeval F (a i))
    Ideal.span (Set.range T) = IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K) ∧
      IsUnit (Matrix.det (fun i j => (MvPowerSeries.pderiv j (T i)).constantCoeff)) := by
  let a : Fin r → MvPolynomial (Fin r ⊕ Fin c) K :=
    fun i => MvPolynomial.X (Sum.inl i) - MvPolynomial.C (y (Sum.inl i))
  let J := I.map (algebraMap _ (Localization.AtPrime Q))
  let : Nontrivial (Localization.AtPrime Q ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
    (polynomial_local_ideal_ne_top I Q hIQ)
  let : IsLocalRing (Localization.AtPrime Q ⧸ J) := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have ha := polynomial_firstOrder_tangents_generate_local_quotient
    I Q hIQ y hQ H htarget h0H hDH
  have hmax : (Q.map (algebraMap _ (Localization.AtPrime Q))).map (Ideal.Quotient.mk J) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q ⧸ J) := by
    exact point_local_quotient_maximalIdeal_map I Q
  have ha' : Ideal.span (Set.range (fun i => Ideal.Quotient.mk J
      (algebraMap _ (Localization.AtPrime Q) (a i)))) =
      (Q.map (algebraMap _ (Localization.AtPrime Q))).map (Ideal.Quotient.mk J) :=
    ha.trans hmax.symm
  exact smooth_actual_unramified_pullback_parameters I P Q x hP F hQP hF
    G hG hJ hlocal hfinite hunram a ha'
end LinearStudy
