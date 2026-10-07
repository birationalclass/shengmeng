module
public import Linear.LocalizedSmoothPointReduction
public import Linear.RationalChartFormalComparison
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace LinearStudy
variable {K : Type*} [Field K] {r c : ℕ} [Nonempty (Fin c)]

def polynomialAwaySmoothFormalMap
    (x : Fin r ⊕ Fin c → K) (p0 : MvPolynomial (Fin r ⊕ Fin c) K)
    (hp0 : MvPolynomial.eval x p0 ≠ 0)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i))))) :
    Localization.Away p0 →+* MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) :=
  ((powerSeriesCoordinateChart K r c).symm.toRingHom.comp
    (polynomialSmoothCoordinateEquiv x G hG hJ).symm.toRingEquiv.toRingHom).comp
      (polynomialAwayFormalMap x p0 hp0).toRingHom

def polynomialAwaySmoothReducedMap
    (x : Fin r ⊕ Fin c → K) (p0 : MvPolynomial (Fin r ⊕ Fin c) K)
    (hp0 : MvPolynomial.eval x p0 ≠ 0)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i))))) :
    Localization.Away p0 →+* MvPowerSeries (Fin r) K :=
  MvPowerSeries.constantCoeff.comp (polynomialAwaySmoothFormalMap x p0 hp0 G hG hJ)

theorem polynomialAwaySmoothFormalMap_algebraMap
    (x : Fin r ⊕ Fin c → K) (p0 : MvPolynomial (Fin r ⊕ Fin c) K)
    (hp0 : MvPolynomial.eval x p0 ≠ 0)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (a : MvPolynomial (Fin r ⊕ Fin c) K) :
    polynomialAwaySmoothFormalMap x p0 hp0 G hG hJ
      (algebraMap _ (Localization.Away p0) a) = polynomialSmoothFormalMap x G hG hJ a := by
  unfold polynomialAwaySmoothFormalMap
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    polynomialAwayFormalMap_algebraMap]
  rfl

theorem polynomialAwaySmoothReducedMap_algebraMap
    (x : Fin r ⊕ Fin c → K) (p0 : MvPolynomial (Fin r ⊕ Fin c) K)
    (hp0 : MvPolynomial.eval x p0 ≠ 0)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (a : MvPolynomial (Fin r ⊕ Fin c) K) :
    polynomialAwaySmoothReducedMap x p0 hp0 G hG hJ
      (algebraMap _ (Localization.Away p0) a) = polynomialSmoothReducedMap x G hG hJ a := by
  unfold polynomialAwaySmoothReducedMap
  rw [RingHom.comp_apply, polynomialAwaySmoothFormalMap_algebraMap]
  rfl

theorem localizedSmoothPointQuotientReduction_away_comparison
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
    (hp0 : MvPolynomial.eval x p0 ≠ 0) :
    (localizedSmoothPointQuotientReduction x p0 I P hP G hG hJ hlocal).comp
      ((Ideal.Quotient.mk _).comp
        (algebraMap (Localization.Away p0) (Localization.AtPrime P))) =
      (MvPowerSeries.constantCoeff.comp
        ((powerSeriesCoordinateChart K r c).symm.toRingHom.comp
          (polynomialSmoothCoordinateEquiv x G hG hJ).symm.toRingEquiv.toRingHom)).comp
        (polynomialAwayFormalMap x p0 hp0).toRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers p0)
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply]
  rw [localizedSmoothPointQuotientReduction_polynomial]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    polynomialAwayFormalMap_algebraMap]
  rfl

end LinearStudy
