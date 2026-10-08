module
public import Linear.ProjectiveCenteredFiberAlgebra
public import Linear.ActualCoordinateFiberPoints
public import Linear.ProjectiveCenteredFiberLocalMaps
public import Linear.RationalLinearNormalLocalSocle
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3600000
namespace LinearStudy
open scoped Matrix
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Assemble the ORIGINAL whole-fiber actual map with its actual polynomial
normal generators. Actual finite ambient quotient, numerator vanishing,
evaluation maps and SAME normal Jacobian socles are all conclusions.
The normal-generator inputs are constructed from the existing original
smooth whole-fiber coordinate presentation, not abstract formal equations. -/
theorem projective_original_whole_fiber_local_socles
    {n r c : ℕ} (hr : 0 < r) (hc : 0 < c)
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet)
    (a : MvPolynomial (Fin n) ℂ)
    (hgood : let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
      let A := Localization.Away (projectiveChartDenominator f V)
      let φ := projectiveChartOpenMap f V hq hf hV x0 hx0
      letI : Algebra B A := φ.toRingHom.toAlgebra
      ∀ P : PrimeSpectrum A, φ (Ideal.Quotient.mk V.affineIdeal a) ∉ P.asIdeal →
        P ∈ Algebra.smoothLocus ℂ A ∧
        PrimeSpectrum.comap φ.toRingHom P ∈ Algebra.smoothLocus ℂ B ∧
        P ∈ Algebra.unramifiedLocus B A)
    (y : Fin n → ℂ) (hy : normalizedProjectivePoint y ∈ V.zeroSet)
    (ha : MvPolynomial.eval y a ≠ 0)
    (E : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (b : Fin n ≃ (Fin r ⊕ Fin c))
    (M : Matrix (Fin r ⊕ Fin c) (Fin r ⊕ Fin c) ℂ) (hM : Matrix.det M ≠ 0)
    (G : (MvPolynomial.zeroLocus ℂ (projectiveAffineFiberIdeal f V y)) →
      Fin c → MvPolynomial (Fin n) ℂ)
    (hG : ∀ x i, MvPolynomial.eval
      (fun j => MvPolynomial.eval x.val (E.symm (MvPolynomial.X j))) (E (G x i)) = 0)
    (hJac : ∀ x, IsUnit (Matrix.det (fun i j => MvPolynomial.eval
      (fun k => MvPolynomial.eval x.val (E.symm (MvPolynomial.X k)))
        (MvPolynomial.pderiv (Sum.inr j) (E (G x i))))))
    (hs : ∀ x : MvPolynomial.zeroLocus ℂ (projectiveAffineFiberIdeal f V y),
      let P := RingHom.ker (MvPolynomial.aeval (R := ℂ) x.val).toRingHom
      letI : P.IsPrime := RingHom.ker_isPrime _
      V.affineIdeal.map (algebraMap _ (Localization.AtPrime P)) =
        Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G x i))))
    (H : Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hH0 : ∀ i, MvPolynomial.eval (0 : Fin r ⊕ Fin c → ℂ) (H i) = 0)
    (hHD : ∀ i j, MvPolynomial.eval (0 : Fin r ⊕ Fin c → ℂ)
      (MvPolynomial.pderiv j (H i)) = if j = Sum.inr i then 1 else 0)
    (ht : let z := M⁻¹ *ᵥ (y ∘ b.symm)
      let I := ((V.affineIdeal.map (MvPolynomial.renameEquiv ℂ b).toRingHom).map
        (polynomialLinearChangeEquiv M hM).toRingHom).map (polynomialTranslation z).toRingHom
      let Q := RingHom.ker (MvPolynomial.aeval (R := ℂ) (0 : Fin r ⊕ Fin c → ℂ)).toRingHom
      letI : Q.IsPrime := RingHom.ker_isPrime _
      I ≤ Q ∧ I.map (algebraMap _ (Localization.AtPrime Q)) =
        Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime Q) (H i)))) :
    let z := M⁻¹ *ᵥ (y ∘ b.symm)
    let p0 := E (affineChartPolynomialMap (f.forms 0))
    let p : (Fin r ⊕ Fin c) → MvPolynomial (Fin r ⊕ Fin c) ℂ :=
      fun j => E (affineChartPolynomialMap (f.forms (b.symm j).succ))
    let pC : (Fin r ⊕ Fin c) → MvPolynomial (Fin r ⊕ Fin c) ℂ :=
      fun i => MvPolynomial.aeval p ((M⁻¹).toMvPolynomial i) - MvPolynomial.C (z i) * p0
    let A := MvPolynomial (Fin r ⊕ Fin c) ℂ ⧸ Ideal.span (Set.range pC)
    let Θ : MvPolynomial (Fin r ⊕ Fin c) ℂ :=
      Matrix.det (fun i j => MvPolynomial.pderiv (Sum.inr j) (pC (Sum.inr i)))
    Module.Finite ℂ A ∧
      ∀ x : MvPolynomial.zeroLocus ℂ (projectiveAffineFiberIdeal f V y),
        let x' := fun j => MvPolynomial.eval x.val (E.symm (MvPolynomial.X j))
        ∃ q : A →ₐ[ℂ] ℂ,
          x' = (fun i => q (Ideal.Quotient.mk _ (MvPolynomial.X i))) ∧
          letI : (RingHom.ker q.toRingHom).IsPrime := RingHom.ker_isPrime _
          let t := algebraMap A (Localization.AtPrime (RingHom.ker q.toRingHom))
            (Ideal.Quotient.mk _ Θ)
          (nilradical (Localization.AtPrime (RingHom.ker q.toRingHom))).annihilator =
            Ideal.span {t} ∧ t ≠ 0 := by
  classical
  letI : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  letI : Nonempty (Fin c) := ⟨⟨0,hc⟩⟩
  intro z p0 p pC A Θ
  have hfinite := projective_actual_centered_fiber_algebra_finite f hq y E b M hM
  letI : Module.Finite ℂ A := hfinite
  letI : IsArtinianRing A := IsArtinianRing.of_finite ℂ A
  obtain ⟨e,he,hlo,hhi,hpoint⟩ := projective_whole_fiber_centered_rational_local_inputs
    f V hq hf hV x0 hx0 a hgood y hy ha E b M hM
  let I := ((V.affineIdeal.map (MvPolynomial.renameEquiv ℂ b).toRingHom).map
    (polynomialLinearChangeEquiv M hM).toRingHom).map (polynomialTranslation z).toRingHom
  let J := V.affineIdeal.map E.toRingHom
  let Q := RingHom.ker (MvPolynomial.aeval (R := ℂ) (0 : Fin r ⊕ Fin c → ℂ)).toRingHom
  letI : Q.IsPrime := RingHom.ker_isPrime _
  refine ⟨hfinite, ?_⟩
  intro x x'
  obtain ⟨hp0,hQP,hu⟩ := hpoint x.val x.property
  let P := RingHom.ker (polynomialAwayPointEvaluation x' p0 hp0).toRingHom
  letI : P.IsPrime := RingHom.ker_isPrime _
  have hp := rational_target_origin_numerators_vanish x' p0 hp0 pC hQP
  obtain ⟨q,hx⟩ := polynomial_equation_quotient_actual_point x' pC hp
  refine ⟨q,hx,?_⟩
  exact rational_linear_normal_common_theta_local_socle x' p0 hp0 pC hp I J P Q
    rfl rfl hQP ht.1 (fun i => E (G x i)) H (hG x) (hJac x)
    (polynomial_coordinate_away_local_generators E x.val V.affineIdeal (G x) (hs x) p0 hp0)
    ht.2 hH0 hHD e he hlo hhi hu hr hc q hx

end LinearStudy
