module
public import Linear.SmoothPolynomialFiber
public import Linear.FormalParameterFiber
public import Linear.SmoothInvariantLocal
public import Linear.SmoothNormalJacobian
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace LinearStudy
variable {r c : ℕ} [Nonempty (Fin c)]

theorem smooth_polynomial_local_fiber_socle
    (I J P Q : Ideal (MvPolynomial (Fin r ⊕ Fin c) ℂ)) [P.IsPrime] [Q.IsPrime]
    [IsArtinianRing (MvPolynomial (Fin r ⊕ Fin c) ℂ ⧸ J)]
    (q : (MvPolynomial (Fin r ⊕ Fin c) ℂ ⧸ J) →ₐ[ℂ] ℂ)
    (x : Fin r ⊕ Fin c → ℂ)
    (hx : x = fun i => q (Ideal.Quotient.mk J (MvPolynomial.X i)))
    (F : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := ℂ) x).toRingHom)
    (hQ : Q = RingHom.ker (MvPolynomial.aeval (R := ℂ)
      (fun i => MvPolynomial.eval x (F i))).toRingHom)
    (hrad : (I.map (MvPolynomial.aeval F).toRingHom).radical = I)
    (G H : Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJac : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hsource : I.map (algebraMap _ (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i))))
    (htarget : I.map (algebraMap _ (Localization.AtPrime Q)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime Q) (H i))))
    (τ : Fin r → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hJ : J = I.map (MvPolynomial.aeval F).toRingHom ⊔ Ideal.span (Set.range τ))
    (hr : 0 < r) (hc : 0 < c)
    (hτ : Ideal.span (Set.range (fun i =>
      (polynomialSmoothFormalMap x G hG hJac (τ i)).constantCoeff)) =
      IsLocalRing.maximalIdeal (ParameterRing r)) :
    letI : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime _
    let θ := Matrix.det (fun i j => MvPolynomial.pderiv (Sum.inr j) (MvPolynomial.aeval F (H i)))
    let a := algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ ⧸ J)
      (Localization.AtPrime (RingHom.ker q.toRingHom)) (Ideal.Quotient.mk J θ)
    (nilradical (Localization.AtPrime (RingHom.ker q.toRingHom))).annihilator =
      Ideal.span {a} ∧ a ≠ 0 := by
  subst x
  let : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime _
  let x := fun i => q (Ideal.Quotient.mk J (MvPolynomial.X i))
  let ψ := polynomialSmoothFormalMap x G hG hJac
  let L := smoothPullbackEquations x G hG hJac F H
  let τ' := fun i => ψ (τ i)
  let θ := Matrix.det (fun i j => MvPolynomial.pderiv (Sum.inr j) (MvPolynomial.aeval F (H i)))
  let Δ := Matrix.det (fun i j => MvPowerSeries.pderiv j (L i))
  have hradL := smooth_invariant_local_pullback_radical I P Q x F hP hQ hrad
    G H hG hJac hsource htarget
  obtain ⟨hArt, hgen, hne⟩ := formal_parameter_fiber_jacobian_socle L hr hc hradL τ' hτ
  have hm : J.map ψ = equationIdeal L ⊔ Ideal.span (Set.range τ') := by
    rw [hJ, Ideal.map_sup,
      polynomialSmoothFormalMap_target_local_generators x G hG hJac F I Q hQ H htarget,
      Ideal.map_span, ← Set.range_comp]
    rfl
  let A := AmbientRing r c ⧸ J.map ψ
  let E0 := Ideal.quotEquivOfEq hm.symm
  have he (z : AmbientRing r c) :
      E0 (Ideal.Quotient.mk (equationIdeal L ⊔ Ideal.span (Set.range τ')) z) =
        Ideal.Quotient.mk (J.map ψ) z := Ideal.quotEquivOfEq_mk _ z
  have hgenA : (nilradical A).annihilator = Ideal.span {Ideal.Quotient.mk (J.map ψ) Δ} := by
    have h := ringEquiv_nilradical_annihilator_generator (C := A) E0 Δ hgen
    rwa [he] at h
  have hneA : Ideal.Quotient.mk (J.map ψ) Δ ≠ 0 := by
    rw [← he]
    intro hz
    exact hne (E0.injective (hz.trans E0.map_zero.symm))
  have hformal : (nilradical A).annihilator = Ideal.span {Ideal.Quotient.mk (J.map ψ) (ψ θ)} := by
    rw [hgenA]
    exact smooth_normal_jacobian_quotient_span x G hG hJac
      (fun i => MvPolynomial.aeval F (H i)) (J.map ψ)
  have hpoly : Ideal.Quotient.mk (J.map ψ) (ψ θ) ≠ 0 :=
    smooth_normal_polynomial_jacobian_nonzero x G hG hJac
      (fun i => MvPolynomial.aeval F (H i)) (J.map ψ) hneA
  have hglobal := smooth_polynomial_formal_socle_generator_descends J q G hG hJac θ hformal
  refine ⟨hglobal, ?_⟩
  let E : A ≃+* Localization.AtPrime (RingHom.ker q.toRingHom) :=
    smoothPolynomialFormalFiberEquiv J q G hG hJac
  have hepoly := smoothPolynomialFormalFiberEquiv_polynomial J q G hG hJac θ
  change E (Ideal.Quotient.mk (J.map ψ) (ψ θ)) = _ at hepoly
  rw [← hepoly]
  intro hz
  exact hpoly (E.injective (hz.trans E.map_zero.symm))

end LinearStudy
