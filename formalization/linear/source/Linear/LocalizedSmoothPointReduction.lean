module
public import Linear.LocalizedPointQuotientEquiv
public import Linear.PolynomialSmoothReduction
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K : Type*} [Field K] {r c : ℕ} [Nonempty (Fin c)]

def localizedSmoothPointQuotientReduction
    (x : Fin r ⊕ Fin c → K) (p0 : MvPolynomial (Fin r ⊕ Fin c) K)
    (I : Ideal (MvPolynomial (Fin r ⊕ Fin c) K))
    (P : Ideal (Localization.Away p0)) [P.IsPrime]
    (hP : P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0)) =
      RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hlocal : I.map (algebraMap _ (Localization.AtPrime
      (P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))))) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime
        (P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0)))) (G i)))) :
    (Localization.AtPrime P ⧸ (I.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))).map
      (algebraMap (Localization.Away p0) (Localization.AtPrime P))) →+*
      MvPowerSeries (Fin r) K :=
  (polynomialSmoothLocalQuotientReduction I
    (P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))) x hP G hG hJ hlocal).comp
      (localizedPointQuotientEquiv (Submonoid.powers p0) I P).symm.toRingHom

theorem localizedSmoothPointQuotientReduction_polynomial
    (x : Fin r ⊕ Fin c → K) (p0 : MvPolynomial (Fin r ⊕ Fin c) K)
    (I : Ideal (MvPolynomial (Fin r ⊕ Fin c) K))
    (P : Ideal (Localization.Away p0)) [P.IsPrime]
    (hP : P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0)) =
      RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hlocal : I.map (algebraMap _ (Localization.AtPrime
      (P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))))) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime
        (P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0)))) (G i))))
    (a : MvPolynomial (Fin r ⊕ Fin c) K) :
    localizedSmoothPointQuotientReduction x p0 I P hP G hG hJ hlocal
      (Ideal.Quotient.mk _ (algebraMap (Localization.Away p0) (Localization.AtPrime P)
        (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0) a))) =
      polynomialSmoothReducedMap x G hG hJ a := by
  let E := localizedPointQuotientEquiv (Submonoid.powers p0) I P
  have he : E.symm (Ideal.Quotient.mk _
      (algebraMap (Localization.Away p0) (Localization.AtPrime P)
        (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0) a))) =
      Ideal.Quotient.mk _ (algebraMap _ (Localization.AtPrime
        (P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0)))) a) := by
    apply E.injective
    rw [E.apply_symm_apply]
    exact (localizedPointQuotientEquiv_mk (Submonoid.powers p0) I P a).symm
  unfold localizedSmoothPointQuotientReduction
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [he, polynomialSmoothLocalQuotientReduction_mk,
    polynomialSmoothPointLocalReduction_polynomial]


theorem localizedSmoothPointQuotient_isLocalRing
    (x : Fin r ⊕ Fin c → K) (p0 : MvPolynomial (Fin r ⊕ Fin c) K)
    (I : Ideal (MvPolynomial (Fin r ⊕ Fin c) K))
    (P : Ideal (Localization.Away p0)) [P.IsPrime]
    (hP : P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0)) =
      RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hlocal : I.map (algebraMap _ (Localization.AtPrime
      (P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))))) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime
        (P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0)))) (G i)))) :
    IsLocalRing (Localization.AtPrime P ⧸ (I.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))).map (algebraMap (Localization.Away p0) (Localization.AtPrime P))) := by
  let E := localizedPointQuotientEquiv (Submonoid.powers p0) I P
  letI := polynomialSmoothLocalQuotient_isLocalRing I
    (P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0)))
    x hP G hG hJ hlocal
  exact E.isLocalRing

theorem localizedSmoothPointQuotientReduction_maximalIdeal
    [Nonempty (Fin r)]
    (x : Fin r ⊕ Fin c → K) (p0 : MvPolynomial (Fin r ⊕ Fin c) K)
    (I : Ideal (MvPolynomial (Fin r ⊕ Fin c) K))
    (P : Ideal (Localization.Away p0)) [P.IsPrime]
    (hP : P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0)) =
      RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hlocal : I.map (algebraMap _ (Localization.AtPrime
      (P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))))) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime
        (P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0)))) (G i)))) :
    letI := localizedSmoothPointQuotient_isLocalRing x p0 I P hP G hG hJ hlocal
    (IsLocalRing.maximalIdeal (Localization.AtPrime P ⧸ (I.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))).map (algebraMap (Localization.Away p0) (Localization.AtPrime P)))).map
      (localizedSmoothPointQuotientReduction x p0 I P hP G hG hJ hlocal) =
        IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K) := by
  let E := localizedPointQuotientEquiv (Submonoid.powers p0) I P
  letI := polynomialSmoothLocalQuotient_isLocalRing I
    (P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0)))
    x hP G hG hJ hlocal
  letI := localizedSmoothPointQuotient_isLocalRing x p0 I P hP G hG hJ hlocal
  have hE := IsLocalRing.map_ringEquiv_maximalIdeal (R := (Localization.AtPrime P ⧸ (I.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))).map (algebraMap (Localization.Away p0) (Localization.AtPrime P)))) (S := (Localization.AtPrime (P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))) ⧸ I.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.AtPrime (P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))))))) E.symm
  unfold localizedSmoothPointQuotientReduction
  rw [← Ideal.map_map]
  simp only [RingEquiv.toRingHom_eq_coe, Ideal.map_coe]
  rw [hE]
  exact local_quotient_reduction_maximalIdeal _ _
    (polynomialSmoothPointLocalReduction_ideal_kernel I _ x hP G hG hJ hlocal)
    (polynomialSmoothPointLocalReduction_maximalIdeal _ x hP G hG hJ)

end LinearStudy
