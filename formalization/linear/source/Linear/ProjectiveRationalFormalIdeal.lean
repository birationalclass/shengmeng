module
public import Linear.ProjectiveRationalInvariance
public import Linear.RationalChartFormalComparison
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual invariant projective ideal has the same formal radical after
rational pullback. The comparison map is constructed by translating the
source point and inverting its nonzero denominator. -/
theorem projective_total_invariance_actual_formal_ratio_radical {n : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hf : f.degree ≠ 0) (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (x : Fin n → ℂ)
    (hp0 : MvPolynomial.eval x (affineChartPolynomialMap (f.forms 0)) ≠ 0) :
    let D := affineChartPolynomialMap (K := ℂ) (n := n)
    let p0 := D (f.forms 0)
    let p := fun i : Fin n => D (f.forms i.succ)
    let I := V.ideal.toIdeal.map D.toRingHom
    ((I.map (rationalPolynomialChartMap p0 p).toRingHom).map
      (polynomialAwayFormalMap x p0 hp0).toRingHom).radical =
        (I.map (formalPolynomialAtPoint x)).radical := by
  intro D p0 p I
  have h := projective_total_invariance_rational_chart_radical f V hf hV
    (polynomialAwayFormalMap x p0 hp0).toRingHom
  change ((I.map (rationalPolynomialChartMap p0 p).toRingHom).map
    (polynomialAwayFormalMap x p0 hp0).toRingHom).radical =
      ((I.map (algebraMap _ (Localization.Away p0))).map
        (polynomialAwayFormalMap x p0 hp0).toRingHom).radical at h
  have he : (polynomialAwayFormalMap x p0 hp0).toRingHom.comp
      (algebraMap _ (Localization.Away p0)) = formalPolynomialAtPoint x := by
    apply RingHom.ext
    intro a
    exact polynomialAwayFormalMap_algebraMap x p0 hp0 a
  conv_rhs at h => rw [Ideal.map_map, he]
  exact h

/-- Actual target point-local equations transfer to the rational formal
pullback. No comparison between those equations and a mapped ideal is assumed. -/
theorem projective_target_equations_actual_formal_radical {n : ℕ}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hf : f.degree ≠ 0) (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (x : Fin n → ℂ)
    (hp0 : MvPolynomial.eval x (affineChartPolynomialMap (f.forms 0)) ≠ 0)
    (Q : Ideal (MvPolynomial (Fin n) ℂ)) [Q.IsPrime]
    (hQ : Q = RingHom.ker (MvPolynomial.aeval (R := ℂ)
      (fun i => MvPolynomial.eval x (affineChartPolynomialMap (f.forms i.succ)) /
        MvPolynomial.eval x (affineChartPolynomialMap (f.forms 0)))).toRingHom)
    {ι : Type*} (H : ι → MvPolynomial (Fin n) ℂ)
    (hlocal : (V.ideal.toIdeal.map affineChartPolynomialMap.toRingHom).map
      (algebraMap _ (Localization.AtPrime Q)) =
        Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime Q) (H i)))) :
    let D := affineChartPolynomialMap (K := ℂ) (n := n)
    let p0 := D (f.forms 0)
    let p := fun i : Fin n => D (f.forms i.succ)
    let I := V.ideal.toIdeal.map D.toRingHom
    (Ideal.span (Set.range (fun i => polynomialAwayFormalMap x p0 hp0
      (rationalPolynomialChartMap p0 p (H i))))).radical =
        (I.map (formalPolynomialAtPoint x)).radical := by
  intro D p0 p I
  have h := projective_total_invariance_actual_formal_ratio_radical f V hf hV x hp0
  change ((I.map (rationalPolynomialChartMap p0 p).toRingHom).map
    (polynomialAwayFormalMap x p0 hp0).toRingHom).radical =
      (I.map (formalPolynomialAtPoint x)).radical at h
  rw [rationalPolynomialChartMap_target_local_generators x p0 hp0 p I Q hQ H hlocal] at h
  exact h

end LinearStudy
