module
public import Linear.RationalUnramifiedParameters
public import Linear.RationalSmoothRadical
public import Linear.RationalLocalEssentialFiniteType
public import Linear.PolynomialLocalParameters
public import Linear.LocalQuotientMaximalIdeal
public import Linear.FirstJetNormalForm
public import Mathlib.RingTheory.RingHom.Unramified
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace LinearStudy

variable {r c : ℕ} [Nonempty (Fin r)] [Nonempty (Fin c)]

/-- The actual linear tangent coordinates generate the actual target local
quotient maximal ideal; no parameter-generation conclusion is assumed. -/
theorem linear_normal_target_local_parameters
    (I Q : Ideal (MvPolynomial (Fin r ⊕ Fin c) ℂ)) [Q.IsPrime]
    (hIQ : I ≤ Q)
    (hQ : Q = RingHom.ker (MvPolynomial.aeval (R := ℂ) (0 : Fin r ⊕ Fin c → ℂ)).toRingHom)
    (H : Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hlocal : I.map (algebraMap _ (Localization.AtPrime Q)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime Q) (H i))))
    (h0 : ∀ i, MvPolynomial.eval (0 : Fin r ⊕ Fin c → ℂ) (H i) = 0)
    (hD : ∀ i j, MvPolynomial.eval (0 : Fin r ⊕ Fin c → ℂ)
      (MvPolynomial.pderiv j (H i)) = if j = Sum.inr i then 1 else 0) :
    Ideal.span (Set.range (fun i : Fin r => Ideal.Quotient.mk _
      (algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ) (Localization.AtPrime Q)
        (MvPolynomial.X (Sum.inl i))))) =
      (Q.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ) (Localization.AtPrime Q))).map
        (Ideal.Quotient.mk (I.map (algebraMap _ (Localization.AtPrime Q)))) := by
  classical
  let J := I.map (algebraMap _ (Localization.AtPrime Q))
  letI : Nontrivial (Localization.AtPrime Q ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
    (polynomial_local_ideal_ne_top I Q hIQ)
  letI : IsLocalRing (Localization.AtPrime Q ⧸ J) := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have h := polynomial_firstOrder_tangents_generate_local_quotient I Q hIQ
    (0 : Fin r ⊕ Fin c → ℂ) hQ H hlocal h0 hD
  simp only [Pi.zero_apply, map_zero, sub_zero] at h
  exact h.trans (point_local_quotient_maximalIdeal_map I Q).symm

/-- Polynomial normal first jets give the formal first-jet hypothesis used by
the relative Jacobian lemma, at the same target origin. -/
theorem linear_normal_target_formal_firstJet
    (H : Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (h0 : ∀ i, MvPolynomial.eval (0 : Fin r ⊕ Fin c → ℂ) (H i) = 0)
    (hD : ∀ i j, MvPolynomial.eval (0 : Fin r ⊕ Fin c → ℂ)
      (MvPolynomial.pderiv j (H i)) = if j = Sum.inr i then 1 else 0) :
    ∀ i, (H i : MvPowerSeries (Fin r ⊕ Fin c) ℂ) - MvPowerSeries.X (Sum.inr i) ∈
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin r ⊕ Fin c) ℂ)) ^ 2 := by
  apply normal_firstOrder_of_derivative_coordinates
  · intro i
    simpa [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq,
      MvPolynomial.coeff_coe, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using h0 i
  · intro i j
    rw [MvPowerSeries.pderiv_coe]
    simpa [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq,
      MvPolynomial.coeff_coe, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hD i j

theorem rational_normal_pullback_formal_comparison
    (x : Fin r ⊕ Fin c → ℂ) (p0 : MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hp0 : MvPolynomial.eval x p0 ≠ 0)
    (p : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hp : ∀ i, MvPolynomial.eval x (p i) = 0)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJac : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (H : Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ) :
    smoothProjectivePullbackEquations x G hG hJac p0 hp0 p hp
      (fun i => (H i : MvPowerSeries (Fin r ⊕ Fin c) ℂ)) =
      (fun i => polynomialAwaySmoothFormalMap x p0 hp0 G hG hJac
        (rationalPolynomialChartMap p0 p (H i))) := by
  funext i
  change polynomialSmoothAmbientEquiv x G hG hJac
    (MvPowerSeries.substAlgHom (R := ℂ) (MvPowerSeries.hasSubst_of_constantCoeff_zero
      (projectiveFormalCoordinateRatios_constantCoeff x p0 hp0 p hp))
        (H i : MvPowerSeries (Fin r ⊕ Fin c) ℂ)) =
    polynomialSmoothAmbientEquiv x G hG hJac
      (polynomialAwayFormalMap x p0 hp0 (rationalPolynomialChartMap p0 p (H i)))
  rw [MvPowerSeries.substAlgHom_coe]
  exact congrArg (polynomialSmoothAmbientEquiv x G hG hJac)
    (AlgHom.congr_fun (rationalPolynomialChartMap_formal_comparison x p0 hp0 p) (H i)).symm

theorem rational_linear_parameters_formal_comparison
    (x : Fin r ⊕ Fin c → ℂ) (p0 : MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hp0 : MvPolynomial.eval x p0 ≠ 0)
    (p : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) ℂ)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJac : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i))))) :
    (fun i => (smoothProjectiveParameterLifts x G hG hJac p0 hp0 p i).constantCoeff) =
      (fun i => polynomialAwaySmoothReducedMap x p0 hp0 G hG hJac
        (rationalPolynomialChartMap p0 p (MvPolynomial.X (Sum.inl i)))) := by
  funext i
  change MvPowerSeries.constantCoeff (polynomialSmoothAmbientEquiv x G hG hJac
    (projectiveFormalCoordinateRatios x p0 hp0 p (Sum.inl i))) =
    MvPowerSeries.constantCoeff (polynomialSmoothAmbientEquiv x G hG hJac
      (polynomialAwayFormalMap x p0 hp0
        (rationalPolynomialChartMap p0 p (MvPolynomial.X (Sum.inl i)))))
  have hh := AlgHom.congr_fun (rationalPolynomialChartMap_formal_comparison x p0 hp0 p)
    (MvPolynomial.X (Sum.inl i))
  simp only [AlgHom.comp_apply, MvPolynomial.aeval_X] at hh
  rw [hh]

/-- Derive BOTH formal input conditions from the actual localized rational
pullback, actual local equations, target linear first jets, unramification and
the actual ideal-power sandwich. Neither a socle nor either formal condition
is supplied as an assumption. The common polynomial is the original normal
Jacobian of p, not a newly chosen local Jacobian. -/
theorem rational_linear_normal_common_theta_formal_socle
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
    (hr : 0 < r) (hc : 0 < c) :
    let ψ := polynomialSmoothFormalMap x G hG hJac
    let Jf := (Ideal.span (Set.range p)).map ψ
    let Θ := Matrix.det (fun i j => MvPolynomial.pderiv (Sum.inr j) (p (Sum.inr i)))
    (nilradical (AmbientRing r c ⧸ Jf)).annihilator =
      Ideal.span {Ideal.Quotient.mk Jf (ψ Θ)} ∧ Ideal.Quotient.mk Jf (ψ Θ) ≠ 0 := by
  classical
  have hPc : P.comap (algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ) (Localization.Away p0)) =
      RingHom.ker (MvPolynomial.aeval (R := ℂ) x).toRingHom := by
    rw [hP]
    exact polynomialAwayPointEvaluation_point_comap x p0 hp0
  have hQratio : Q = RingHom.ker (MvPolynomial.aeval (R := ℂ)
      (fun i => MvPolynomial.eval x (p i) / MvPolynomial.eval x p0)).toRingHom := by
    simpa only [hp, zero_div, Pi.zero_def] using hQ
  have hrad := rational_smooth_actual_normal_radical x p0 hp0 p I J _ Q hPc hQratio
    G H hG hJac hsource htarget e he hlo hhi
  have hfirst := linear_normal_target_formal_firstJet H hH0 hHD
  have hL := rational_normal_pullback_formal_comparison x p0 hp0 p hp G hG hJac H
  have hrad' : (equationIdeal (smoothProjectivePullbackEquations x G hG hJac p0 hp0 p hp
      (fun i => (H i : MvPowerSeries (Fin r ⊕ Fin c) ℂ)))).radical =
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c) (R := ParameterRing r))) := by
    rw [equationIdeal, hL]
    exact hrad
  have ha := linear_normal_target_local_parameters I Q hIQ hQ H htarget hH0 hHD
  have hfinite := rationalPointLocalQuotientPullback_essFiniteType p0 p I J P Q hQP hhi
  have hu : letI := (generalPointLocalQuotientPullback I
      (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ) (Localization.Away p0))) P Q
      (rationalPolynomialChartMap p0 p).toRingHom hQP hhi).toAlgebra
      Algebra.FormallyUnramified
        (Localization.AtPrime Q ⧸ I.map (algebraMap _ (Localization.AtPrime Q)))
        (Localization.AtPrime P ⧸
          (J.map (algebraMap (MvPolynomial (Fin r ⊕ Fin c) ℂ) (Localization.Away p0))).map
            (algebraMap (Localization.Away p0) (Localization.AtPrime P))) := hunram
  have hpar := (rational_unramified_actual_formal_parameters x p0 hp0 p I J P Q
    hP hQP hhi G hG hJac hsource hfinite hu (fun i => MvPolynomial.X (Sum.inl i)) ha).1
  have hτ : Ideal.span (Set.range (fun i =>
      (smoothProjectiveParameterLifts x G hG hJac p0 hp0 p i).constantCoeff)) =
        IsLocalRing.maximalIdeal (ParameterRing r) := by
    rw [rational_linear_parameters_formal_comparison]
    exact hpar
  exact smooth_projective_common_theta_formal_socle x G hG hJac p0 hp0 p hp
    (fun i => (H i : MvPowerSeries (Fin r ⊕ Fin c) ℂ)) hfirst hr hc hrad' hτ

end LinearStudy
