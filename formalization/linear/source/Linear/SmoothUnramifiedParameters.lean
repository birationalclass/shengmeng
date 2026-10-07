module
public import Linear.SmoothTargetParameters
public import Linear.LocalQuotientMaximalIdeal
public import Linear.ActualUnramifiedPullback
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

/-- Actual smoothness of the target constructs its polynomial parameters;
the actual unramified local pullback yields source formal parameters. -/
theorem smooth_target_constructs_unramified_pullback_parameters
    {K : Type*} [Field K] {r c : ℕ} [Nonempty (Fin r)] [Nonempty (Fin c)]
    (I P : Ideal (MvPolynomial (Fin r ⊕ Fin c) K)) [I.IsPrime] [P.IsPrime] (hI : I ≠ ⊥)
    (p : Ideal (MvPolynomial (Fin r ⊕ Fin c) K ⧸ I)) [p.IsPrime] [Algebra.IsSmoothAt K p]
    (x y : Fin r ⊕ Fin c → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (hp : p.comap (Ideal.Quotient.mk I) =
      RingHom.ker (MvPolynomial.aeval (R := K) y).toRingHom)
    (hr : r = Module.finrank (MvPolynomial (Fin r ⊕ Fin c) K ⧸ I)
      (KaehlerDifferential K (MvPolynomial (Fin r ⊕ Fin c) K ⧸ I)))
    (F : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hQP : p.comap (Ideal.Quotient.mk I) = P.comap (MvPolynomial.aeval F).toRingHom)
    (hF : I.map (MvPolynomial.aeval F).toRingHom ≤ I)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hlocal : I.map (algebraMap _ (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i))))
    (hfinite : letI := (pointLocalQuotientPullback I P (p.comap (Ideal.Quotient.mk I))
        (MvPolynomial.aeval F).toRingHom hQP hF).toAlgebra
      Algebra.EssFiniteType
        (Localization.AtPrime (p.comap (Ideal.Quotient.mk I)) ⧸
          I.map (algebraMap _ (Localization.AtPrime (p.comap (Ideal.Quotient.mk I)))))
        (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))))
    (hunram : letI := (pointLocalQuotientPullback I P (p.comap (Ideal.Quotient.mk I))
        (MvPolynomial.aeval F).toRingHom hQP hF).toAlgebra
      Algebra.FormallyUnramified
        (Localization.AtPrime (p.comap (Ideal.Quotient.mk I)) ⧸
          I.map (algebraMap _ (Localization.AtPrime (p.comap (Ideal.Quotient.mk I)))))
        (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P)))) :
    ∃ a : Fin r → MvPolynomial (Fin r ⊕ Fin c) K,
      let T := fun i => polynomialSmoothReducedMap x G hG hJ (MvPolynomial.aeval F (a i))
      Ideal.span (Set.range T) = IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K) ∧
        IsUnit (Matrix.det (fun i j => (MvPowerSeries.pderiv j (T i)).constantCoeff)) := by
  let Q := p.comap (Ideal.Quotient.mk I)
  let : Q.IsPrime := inferInstance
  have hIQ : I ≤ Q := by
    intro F hF
    change Ideal.Quotient.mk I F ∈ p
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hF]
    exact p.zero_mem
  let J := I.map (algebraMap _ (Localization.AtPrime Q))
  let : Nontrivial (Localization.AtPrime Q ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
    (polynomial_local_ideal_ne_top I Q hIQ)
  let : IsLocalRing (Localization.AtPrime Q ⧸ J) := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  obtain ⟨s, a, hs, ha⟩ := smoothLocus_constructs_original_polynomial_parameters I hI p y hp
  have hsr : s = r := hs.trans hr.symm
  clear hs
  subst s
  have ha' : Ideal.span (Set.range (fun i => Ideal.Quotient.mk J
      (algebraMap _ (Localization.AtPrime Q) (a i)))) =
      (Q.map (algebraMap _ (Localization.AtPrime Q))).map (Ideal.Quotient.mk J) :=
    ha.trans (point_local_quotient_maximalIdeal_map I Q).symm
  exact ⟨a, smooth_actual_unramified_pullback_parameters I P Q x hP F hQP hF
    G hG hJ hlocal hfinite hunram a ha'⟩
end LinearStudy
