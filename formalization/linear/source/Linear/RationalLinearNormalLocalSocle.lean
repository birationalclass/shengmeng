module
public import Linear.RationalLinearNormalSocle
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace LinearStudy
variable {r c : ℕ} [Nonempty (Fin r)] [Nonempty (Fin c)]

/-- The SAME original polynomial normal Jacobian generates the annihilator
in the actual localized Artinian polynomial fiber algebra, after the derived
formal conditions are checked. No local socle conclusion is assumed. -/
theorem rational_linear_normal_common_theta_local_socle
    (x : Fin r ⊕ Fin c → ℂ) (p0 : MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hp0 : MvPolynomial.eval x p0 ≠ 0)
    (p : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hp : ∀ i, MvPolynomial.eval x (p i) = 0)
    (I J : Ideal (MvPolynomial (Fin r ⊕ Fin c) ℂ))
    (P : Ideal (Localization.Away p0)) (Q : Ideal (MvPolynomial (Fin r ⊕ Fin c) ℂ))
    [P.IsPrime] [Q.IsPrime]
    (hP : P = RingHom.ker (polynomialAwayPointEvaluation x p0 hp0).toRingHom)
    (hQ : Q = RingHom.ker (MvPolynomial.aeval (R := ℂ) (0 : Fin r ⊕ Fin c → ℂ)).toRingHom)
    (hQP : Q = P.comap (rationalPolynomialChartMap p0 p).toRingHom)
    (hIQ : I ≤ Q)
    (G H : Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJac : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hsource : J.map (algebraMap _ (Localization.AtPrime
      (P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ) (Localization.Away p0))))) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime
        (P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ) (Localization.Away p0)))) (G i))))
    (htarget : I.map (algebraMap _ (Localization.AtPrime Q)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime Q) (H i))))
    (hH0 : ∀ i, MvPolynomial.eval (0 : Fin r ⊕ Fin c → ℂ) (H i) = 0)
    (hHD : ∀ i j, MvPolynomial.eval (0 : Fin r ⊕ Fin c → ℂ)
      (MvPolynomial.pderiv j (H i)) = if j = Sum.inr i then 1 else 0)
    (e : ℕ) (he : 0 < e)
    (hlo : (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ) (Localization.Away p0))) ^ e ≤
      I.map (rationalPolynomialChartMap p0 p).toRingHom)
    (hhi : I.map (rationalPolynomialChartMap p0 p).toRingHom ≤
      J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ) (Localization.Away p0)))
    (hunram : (generalPointLocalQuotientPullback I
      (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ) (Localization.Away p0))) P Q
      (rationalPolynomialChartMap p0 p).toRingHom hQP hhi).FormallyUnramified)
    (hr : 0 < r) (hc : 0 < c)
    [IsArtinianRing (MvPolynomial (Fin r ⊕ Fin c) ℂ ⧸ Ideal.span (Set.range p))]
    (q : (MvPolynomial (Fin r ⊕ Fin c) ℂ ⧸ Ideal.span (Set.range p)) →ₐ[ℂ] ℂ)
    (hx : x = fun i => q (Ideal.Quotient.mk (Ideal.span (Set.range p)) (MvPolynomial.X i))) :
    letI : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime _
    let Θ := Matrix.det (fun i j => MvPolynomial.pderiv (Sum.inr j) (p (Sum.inr i)))
    let a := algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ ⧸ Ideal.span (Set.range p))
      (Localization.AtPrime (RingHom.ker q.toRingHom))
        (Ideal.Quotient.mk (Ideal.span (Set.range p)) Θ)
    (nilradical (Localization.AtPrime (RingHom.ker q.toRingHom))).annihilator =
      Ideal.span {a} ∧ a ≠ 0 := by
  subst x
  letI : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime _
  let x := fun i => q (Ideal.Quotient.mk (Ideal.span (Set.range p)) (MvPolynomial.X i))
  let Θ := Matrix.det (fun i j => MvPolynomial.pderiv (Sum.inr j) (p (Sum.inr i)))
  obtain ⟨hgen, hne⟩ := rational_linear_normal_common_theta_formal_socle
    x p0 hp0 p hp I J P Q hP hQ hQP hIQ G H hG hJac hsource htarget hH0 hHD
    e he hlo hhi hunram hr hc
  have hlocal := smooth_polynomial_formal_socle_generator_descends
    (Ideal.span (Set.range p)) q G hG hJac Θ hgen
  refine ⟨hlocal, ?_⟩
  let A := AmbientRing r c ⧸ (Ideal.span (Set.range p)).map (polynomialSmoothFormalMap x G hG hJac)
  let E : A ≃+* Localization.AtPrime (RingHom.ker q.toRingHom) :=
    smoothPolynomialFormalFiberEquiv (Ideal.span (Set.range p)) q G hG hJac
  have heq := smoothPolynomialFormalFiberEquiv_polynomial (Ideal.span (Set.range p)) q G hG hJac Θ
  change E (Ideal.Quotient.mk _ (polynomialSmoothFormalMap x G hG hJac Θ)) = _ at heq
  rw [← heq]
  intro hz
  exact hne (E.injective (hz.trans E.map_zero.symm))

end LinearStudy
