module
public import Linear.RationalSmoothReduction
public import Linear.PowerSeriesThickeningReduction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace LinearStudy
variable {K : Type*} [Field K] {r c : ℕ} [Nonempty (Fin c)]
attribute [local instance] NoZeroDivisors.to_isDomain

/-- A derived rational pullback power sandwich and actual point-local smooth
equations identify the normal radical in the constructed smooth coordinates. -/
theorem rational_smooth_actual_normal_radical
    (x : Fin r ⊕ Fin c → K) (p0 : MvPolynomial (Fin r ⊕ Fin c) K)
    (hp0 : MvPolynomial.eval x p0 ≠ 0) (p : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (I J P Q : Ideal (MvPolynomial (Fin r ⊕ Fin c) K)) [P.IsPrime] [Q.IsPrime]
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (hQ : Q = RingHom.ker (MvPolynomial.aeval (R := K)
      (fun i => MvPolynomial.eval x (p i) / MvPolynomial.eval x p0)).toRingHom)
    (G H : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hsource : J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.AtPrime P) (G i))))
    (htarget : I.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.AtPrime Q)) =
      Ideal.span (Set.range (fun i => algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.AtPrime Q) (H i))))
    (e : ℕ) (he : 0 < e)
    (hlo : (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))) ^ e ≤ I.map (rationalPolynomialChartMap p0 p).toRingHom)
    (hhi : I.map (rationalPolynomialChartMap p0 p).toRingHom ≤ (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0)))) :
    (Ideal.span (Set.range (fun i => polynomialAwaySmoothFormalMap x p0 hp0 G hG hJ
      (rationalPolynomialChartMap p0 p (H i))))).radical =
        Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c) (R := MvPowerSeries (Fin r) K))) := by
  let ψ := polynomialAwaySmoothFormalMap x p0 hp0 G hG hJ
  have hunit : ∀ a : Q.primeCompl,
      IsUnit ((ψ.comp (rationalPolynomialChartMap p0 p).toRingHom) a) := by
    intro a
    have ha : MvPolynomial.eval
        (fun i => MvPolynomial.eval x (p i) / MvPolynomial.eval x p0) a ≠ 0 := by
      intro hz
      apply a.property
      exact (congrArg (fun L : Ideal (MvPolynomial (Fin r ⊕ Fin c) K) => (a : MvPolynomial (Fin r ⊕ Fin c) K) ∈ L) hQ).mpr hz
    have hu := (rationalPolynomialChartMap_formal_isUnit_iff x p0 hp0 p a).mpr ha
    exact ((powerSeriesCoordinateChart K r c).symm.toRingHom.comp
      (polynomialSmoothCoordinateEquiv x G hG hJ).symm.toRingEquiv.toRingHom).isUnit_map hu
  have ht : (I.map (rationalPolynomialChartMap p0 p).toRingHom).map ψ =
      Ideal.span (Set.range (fun i => ψ (rationalPolynomialChartMap p0 p (H i)))) := by
    rw [Ideal.map_map]
    exact local_ideal_generators_image I Q H (ψ.comp (rationalPolynomialChartMap p0 p).toRingHom) hunit htarget
  have hs : (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0))).map ψ =
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c) (R := MvPowerSeries (Fin r) K))) := by
    rw [Ideal.map_map]
    have hcomp : ψ.comp (algebraMap (MvPolynomial (Fin r ⊕ Fin c) K) (Localization.Away p0)) =
        polynomialSmoothFormalMap x G hG hJ := by
      apply RingHom.ext
      intro a
      exact polynomialAwaySmoothFormalMap_algebraMap x p0 hp0 G hG hJ a
    rw [hcomp]
    exact polynomialSmoothFormalMap_local_ideal J P x hP G hG hJ hsource
  have hu := Ideal.map_mono (f := ψ) hhi
  have hl := Ideal.map_mono (f := ψ) hlo
  rw [ht, hs] at hu
  rw [Ideal.map_pow, ht, hs] at hl
  exact powerSeries_thickening_radical _ e he hu hl

end LinearStudy
