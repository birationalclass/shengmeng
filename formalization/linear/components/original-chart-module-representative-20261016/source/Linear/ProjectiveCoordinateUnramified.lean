module
public import Linear.ProjectiveAmbientAtPoint
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy
variable {n : ℕ}

theorem generalPointLocalQuotientPullback_unramified_transport
    {R A : Type*} [CommRing R] [CommRing A]
    (I : Ideal R) (J : Ideal A) (φ : R →+* A) (hφ : I.map φ ≤ J)
    (P P' : Ideal A) (Q Q' : Ideal R)
    [P.IsPrime] [P'.IsPrime] [Q.IsPrime] [Q'.IsPrime]
    (hP : P = P') (hQ : Q = Q')
    (hq : Q = P.comap φ) (hq' : Q' = P'.comap φ)
    (h : (generalPointLocalQuotientPullback I J P Q φ hq hφ).FormallyUnramified) :
    (generalPointLocalQuotientPullback I J P' Q' φ hq' hφ).FormallyUnramified := by
  subst P'
  subst Q'
  exact h

/-- The actual coordinate point has the same unramified ambient local map. -/
theorem projectiveAmbientChart_unramified_at_affine_coordinates
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x0 : Fin n → ℂ)
    (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet)
    (ρ : Localization.Away (projectiveChartDenominator f V) →ₐ[ℂ] ℂ)
    (hρ : let φ := projectiveChartOpenMap f V hq hf hV x0 hx0
      letI : Algebra (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
        (Localization.Away (projectiveChartDenominator f V)) := φ.toRingHom.toAlgebra
      rationalPointPrime ρ ∈ Algebra.unramifiedLocus
        (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
        (Localization.Away (projectiveChartDenominator f V)))
    (x : Fin n → ℂ)
    (hx : (ρ.comp (IsScalarTower.toAlgHom ℂ
      (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal)
      (Localization.Away (projectiveChartDenominator f V)))).comp
        (Ideal.Quotient.mkₐ ℂ V.affineIdeal) = MvPolynomial.aeval x)
    (hp0 : MvPolynomial.eval x (affineChartPolynomialMap (f.forms 0)) ≠ 0) :
    let p0 := affineChartPolynomialMap (f.forms 0)
    let p := fun i : Fin n => affineChartPolynomialMap (f.forms i.succ)
    let J := V.affineIdeal.map (algebraMap _ (Localization.Away p0))
    let P := RingHom.ker (polynomialAwayPointEvaluation x p0 hp0).toRingHom
    letI : P.IsPrime := RingHom.ker_isPrime _
    let Q := P.comap (rationalPolynomialChartMap p0 p).toRingHom
    let hI := projectiveRationalPolynomialChartMap_ideal f V hq hf hV x0 hx0
    (generalPointLocalQuotientPullback V.affineIdeal J P Q
      (rationalPolynomialChartMap p0 p).toRingHom rfl hI).FormallyUnramified := by
  intro p0 p J P
  letI : P.IsPrime := RingHom.ker_isPrime _
  intro Q hI
  let E := awayQuotientEquiv V.affineIdeal p0
  let ψ := Ideal.quotientMap J (rationalPolynomialChartMap p0 p).toRingHom
    (Ideal.map_le_iff_le_comap.mp hI)
  let Pc := (rationalPointPrime ρ).asIdeal.comap E.toRingHom
  have he := projectiveChartOpenMap_ambient_rational_evaluation f V ρ x hx hp0
  have hPc : Pc.comap (Ideal.Quotient.mk J) = P := by
    change (RingHom.ker ρ.toRingHom).comap
      ((awayQuotientBaseEquiv (K := ℂ) V.affineIdeal p0).toAlgHom.comp
        (Ideal.Quotient.mkₐ ℂ J)).toRingHom = P
    rw [RingHom.comap_ker]
    exact congrArg (fun a : Localization.Away p0 →ₐ[ℂ] ℂ => RingHom.ker a.toRingHom) he
  have hQ : (Pc.comap ψ).comap (Ideal.Quotient.mk V.affineIdeal) = Q := by
    have hcomp : (Pc.comap ψ).comap (Ideal.Quotient.mk V.affineIdeal) =
        (Pc.comap (Ideal.Quotient.mk J)).comap (rationalPolynomialChartMap p0 p).toRingHom := by
      ext H
      rfl
    rw [hcomp, hPc]
  have h := projectiveAmbientChart_unramified_at_rational_point f V hq hf hV x0 hx0 ρ hρ
  change (generalPointLocalQuotientPullback V.affineIdeal J
    (Pc.comap (Ideal.Quotient.mk J))
    ((Pc.comap ψ).comap (Ideal.Quotient.mk V.affineIdeal))
    (rationalPolynomialChartMap p0 p).toRingHom (by ext H; rfl) hI).FormallyUnramified at h
  exact generalPointLocalQuotientPullback_unramified_transport V.affineIdeal J
    (rationalPolynomialChartMap p0 p).toRingHom hI _ P _ Q hPc hQ _ rfl h

/-- A smooth source and image on the original variety, with unramification at
the actual coordinate local quotient map, are constructed together. -/
theorem projectiveChart_exists_smooth_unramified_coordinate_point
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x0 : Fin n → ℂ)
    (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :
    let p0 := affineChartPolynomialMap (f.forms 0)
    let p := fun i : Fin n => affineChartPolynomialMap (f.forms i.succ)
    let J := V.affineIdeal.map (algebraMap _ (Localization.Away p0))
    let hI := projectiveRationalPolynomialChartMap_ideal f V hq hf hV x0 hx0
    ∃ (x : Fin n → ℂ) (hx : normalizedProjectivePoint x ∈ V.zeroSet)
      (hp0 : MvPolynomial.eval x p0 ≠ 0),
      let y := fun i => MvPolynomial.eval x (p i) / MvPolynomial.eval x p0
      ∃ hy : normalizedProjectivePoint y ∈ V.zeroSet,
        Algebra.IsSmoothAt ℂ (V.affinePoint x hx).asIdeal ∧
        Algebra.IsSmoothAt ℂ (V.affinePoint y hy).asIdeal ∧
        let P := RingHom.ker (polynomialAwayPointEvaluation x p0 hp0).toRingHom
        letI : P.IsPrime := RingHom.ker_isPrime _
        let Q := P.comap (rationalPolynomialChartMap p0 p).toRingHom
        (generalPointLocalQuotientPullback V.affineIdeal J P Q
          (rationalPolynomialChartMap p0 p).toRingHom rfl hI).FormallyUnramified := by
  intro p0 p J hI
  obtain ⟨ρ, x, hx, hp0, hy, hs, ht, hu, heval, _⟩ :=
    projectiveChartOpenMap_exists_good_affine_coordinates f V hq hf hV x0 hx0
  exact ⟨x, hx, hp0, hy, hs, ht,
    projectiveAmbientChart_unramified_at_affine_coordinates f V hq hf hV x0 hx0
      ρ hu x heval hp0⟩

end LinearStudy
