module
public import Linear.RationalLocalEssentialFiniteType
public import Linear.RationalSmoothJacobianSocle
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace LinearStudy
variable {r c : ℕ} [Nonempty (Fin r)] [Nonempty (Fin c)]
attribute [local instance] NoZeroDivisors.to_isDomain

/-- Actual rational polynomial local quotient maps supply essential finite
type automatically; only the genuine local geometric conditions remain. -/
theorem rational_smooth_unramified_socle_without_finite_type_input
    (x : Fin r ⊕ Fin c → ℂ) (p0 : MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hp0 : MvPolynomial.eval x p0 ≠ 0) (p : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (I J : Ideal (MvPolynomial (Fin r ⊕ Fin c) ℂ)) [I.IsPrime] (hI : I ≠ ⊥)
    (P : Ideal (Localization.Away p0)) [P.IsPrime]
    (p' : Ideal (MvPolynomial (Fin r ⊕ Fin c) ℂ ⧸ I)) [p'.IsPrime] [Algebra.IsSmoothAt ℂ p']
    (hp : (p'.comap (Ideal.Quotient.mk I)) = RingHom.ker (MvPolynomial.aeval (R := ℂ)
      (fun i => MvPolynomial.eval x (p i) / MvPolynomial.eval x p0)).toRingHom)
    (hr : r = Module.finrank (MvPolynomial (Fin r ⊕ Fin c) ℂ ⧸ I) (KaehlerDifferential ℂ (MvPolynomial (Fin r ⊕ Fin c) ℂ ⧸ I)))
    (hP : P = RingHom.ker (polynomialAwayPointEvaluation x p0 hp0).toRingHom)
    (hQP : (p'.comap (Ideal.Quotient.mk I)) = P.comap (rationalPolynomialChartMap p0 p).toRingHom)
    (hφ : I.map (rationalPolynomialChartMap p0 p).toRingHom ≤ (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ) (Localization.Away p0))))
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hlocal : J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ) (Localization.AtPrime
      (P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ) (Localization.Away p0))))) =
      Ideal.span (Set.range (fun i => algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ) (Localization.AtPrime
        (P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ) (Localization.Away p0)))) (G i))))
    (hunram : letI := (generalPointLocalQuotientPullback I (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ) (Localization.Away p0))) P (p'.comap (Ideal.Quotient.mk I)) (rationalPolynomialChartMap p0 p).toRingHom hQP hφ).toAlgebra
      Algebra.FormallyUnramified (Localization.AtPrime (p'.comap (Ideal.Quotient.mk I)) ⧸ I.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ) (Localization.AtPrime (p'.comap (Ideal.Quotient.mk I))))) (Localization.AtPrime P ⧸ (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ) (Localization.Away p0))).map (algebraMap (Localization.Away p0) (Localization.AtPrime P))))

    (H : Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (htarget : I.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ) (Localization.AtPrime (p'.comap (Ideal.Quotient.mk I)))) =
      Ideal.span (Set.range (fun i => algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ) (Localization.AtPrime (p'.comap (Ideal.Quotient.mk I))) (H i))))
    (e : ℕ) (he : 0 < e)
    (hlo : (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ) (Localization.Away p0))) ^ e ≤ I.map (rationalPolynomialChartMap p0 p).toRingHom)
    (hhi : I.map (rationalPolynomialChartMap p0 p).toRingHom ≤ (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ) (Localization.Away p0)))) :
    let HF : Fin c → AmbientRing r c := fun i => polynomialAwaySmoothFormalMap x p0 hp0 G hG hJ
      (rationalPolynomialChartMap p0 p (H i))
    ∃ a : Fin r → MvPolynomial (Fin r ⊕ Fin c) ℂ,
      let τ : Fin r → CompleteIntersection HF := fun i => Ideal.Quotient.mk (equationIdeal HF)
        (polynomialAwaySmoothFormalMap x p0 hp0 G hG hJ
          (rationalPolynomialChartMap p0 p (a i)))
      let L : Ideal (CompleteIntersection HF) := Ideal.span (Set.range τ)
      let C := CompleteIntersection HF ⧸ L
      let m := (nilradical (CompleteIntersection HF)).map (Ideal.Quotient.mk L)
      IsArtinianRing C ∧ m.IsMaximal ∧
        m.annihilator = Ideal.span {Ideal.Quotient.mk L (relativeJacobian HF)} ∧
        Ideal.Quotient.mk L (relativeJacobian HF) ≠ 0 := by
  have hfinite := rationalPointLocalQuotientPullback_essFiniteType p0 p I J P
    (p'.comap (Ideal.Quotient.mk I)) hQP hφ
  exact rational_smooth_unramified_constructs_jacobian_socle x p0 hp0 p I J hI
    P p' hp hr hP hQP hφ G hG hJ hlocal hfinite hunram H htarget e he hlo hhi

end LinearStudy
